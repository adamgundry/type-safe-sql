{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module TypeSafeSQL where

import Data.Kind (Type, Constraint)
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels
import GHC.TypeLits


type Database   = [Table]
data Table      = TableName := [Column]
data Column     = ColumnName ::: Type
type TableName  = Symbol
type ColumnName = Symbol


-- SELECT [DISTINCT | ALL] result-column*
--   [FROM (table-or-subquery* | join-clause)] [WHERE expr] [GROUP BY expr* [HAVING expr]]
--   [ORDER BY ordering-term*] [LIMIT expr [OFFSET expr]]

-- result-column ::= * | expr [AS column-alias] | table-name . *

data SelectQuery = Select { resultColumns :: [ResultColumn]
                          , fromClause    :: TableExpr
                          , whereClause   :: WhereClause
                          }

data TableExpr = From TableName
               | CrossJoin TableExpr TableExpr
               | LeftJoinUsing TableExpr TableExpr [ColumnName]

type WhereClause  = Maybe Expression
type AsClause     = Maybe ColumnName
data ResultColumn = Star | Expr Expression AsClause
data Expression   = Lit | Col ColumnName


data family Sing k :: k -> Type
data instance Sing [k] xs where
  Nil_ :: Sing [k] '[]
  (:>) :: Sing k x -> Sing [k] xs -> Sing [k] (x ': xs)
infixr 5 :>
data instance Sing (Maybe k) x where
  Nothing_ :: Sing (Maybe k) Nothing
  Just_    :: Sing k x -> Sing (Maybe k) (Just x)
data instance Sing Symbol s where
  Symbol :: KnownSymbol s => Proxy# s -> Sing Symbol s

data instance Sing SelectQuery q where
  Select_ :: Sing [ResultColumn] rcs -> Sing TableExpr te -> Sing WhereClause wc
          -> Sing SelectQuery (Select rcs te wc)
data instance Sing ResultColumn rc where
  Star_ :: Sing ResultColumn Star
  Expr_ :: Sing Expression e -> Sing AsClause a -> Sing ResultColumn (Expr e a)
data instance Sing TableExpr te where
  From_ :: Sing TableName t -> Sing TableExpr (From t)
  CrossJoin_ :: Sing TableExpr te1 -> Sing TableExpr te2 -> Sing TableExpr (CrossJoin te1 te2)
  LeftJoinUsing_ :: Sing TableExpr te1 -> Sing TableExpr te2 -> Sing [ColumnName] cols -> Sing TableExpr (LeftJoinUsing te1 te2 cols)
data instance Sing Expression e where
  Lit_ :: Int -> Sing Expression Lit
  Col_ :: Sing ColumnName c -> Sing Expression (Col c)


instance (s ~ x, KnownSymbol s) => IsLabel x (Sing Symbol s) where
  fromLabel = Symbol


class ToQuery k where
  toQuery :: Sing k e -> String

instance ToQuery Symbol where
  toQuery (Symbol p) = symbolVal' p

maybeToQuery :: ToQuery k => String -> Sing (Maybe k) x -> String
maybeToQuery _ Nothing_ = ""
maybeToQuery s (Just_ x) = " " ++ s ++ " " ++ toQuery x

instance ToQuery k => ToQuery [k] where
  toQuery Nil_        = ""
  toQuery (x :> Nil_) = toQuery x
  toQuery (x :> xs)   = toQuery x ++ ", " ++ toQuery xs

instance ToQuery SelectQuery where
  toQuery (Select_ rcs t mb_w) =
      "SELECT (" ++ toQuery rcs ++ ") FROM " ++ toQuery t ++ maybeToQuery "WHERE" mb_w

instance ToQuery TableExpr where
  toQuery (From_ t) = toQuery t
  toQuery (CrossJoin_ te1 te2) = toQuery te1 ++ " CROSS JOIN " ++ toQuery te2
  toQuery (LeftJoinUsing_ te1 te2 cols) = toQuery te1 ++ " LEFT OUTER JOIN " ++ toQuery te2 ++ " USING " ++ toQuery cols

instance ToQuery ResultColumn where
  toQuery Star_ = "*"
  toQuery (Expr_ e mb_a) = toQuery e ++ maybeToQuery "AS" mb_a

instance ToQuery Expression where
  toQuery (Lit_ k) = show k
  toQuery (Col_ c) = toQuery c



type family If b x y where
  If True x _ = x
  If _    _ y = y

type family Elem x xs where
  Elem x '[] = False
  Elem x (x ': xs) = True
  Elem x (_ ': xs) = Elem x xs

type family (++) xs ys where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)


type family QueryColumnsDB (db :: Database) (q :: SelectQuery) :: [Column] where
  QueryColumnsDB db (Select rcs te _wc) = LookupResultColumns rcs (ExpandTableExpr db te)

type family ExpandTableExpr (db :: Database) (te :: TableExpr) :: [Column] where
  ExpandTableExpr db (From t) = LookupTable t db
  ExpandTableExpr db (CrossJoin te1 te2) = ExpandTableExpr db te1 ++ ExpandTableExpr db te2
  ExpandTableExpr db (LeftJoinUsing te1 te2 cols) = LookupColumns cols (ExpandTableExpr db te1)
                                                 ++ FilterColumns cols (ExpandTableExpr db te1)
                                                 ++ FilterColumns cols (ExpandTableExpr db te2)

type family LookupResultColumns (rcs :: [ResultColumn]) (cols :: [Column]) :: [Column] where
  LookupResultColumns '[] cols = '[]
  LookupResultColumns (Star ': rcs) cols = cols
  LookupResultColumns ('Expr e Nothing  ': rcs) cols = (ExprName e ::: ExprType e cols) ': LookupResultColumns rcs cols
  LookupResultColumns ('Expr e (Just c) ': rcs) cols = (c ::: ExprType e cols) ': LookupResultColumns rcs cols

type family ExprName e where
  ExprName Lit = "" -- ?
  ExprName (Col c) = c

type family ExprType e cols where
  ExprType Lit cols = Int -- ?
  ExprType (Col c) cols = LookupColumn c cols

type family LookupTable (table :: TableName) (db :: Database) :: [Column] where
  LookupTable table '[] = TypeError (Text "Table " :<>: ShowType table :<>: Text " missing")
  LookupTable table ((table := cols) ': _) = cols
  LookupTable table (_ ': db) = LookupTable table db

type family LookupColumns colnames cols :: [Column] where
  LookupColumns '[] cols = '[]
  LookupColumns (colname ': colnames) cols = (colname ::: LookupColumn colname cols) ': LookupColumns colnames cols

type family LookupColumn colname cols :: Type where
  LookupColumn colname '[] = TypeError (Text "Column " :<>: ShowType colname :<>: Text " missing")
  LookupColumn colname ((colname ::: ty) ': _) = ty
  LookupColumn colname (_ ': cols) = LookupColumn colname cols

type family FilterColumns (colnames :: [ColumnName]) (cols :: [Column]) :: [Column] where
  FilterColumns colnames '[] = '[]
  FilterColumns colnames ((colname ::: ty) ': cols) = If (colname `Elem` colnames) (FilterColumns colnames cols)
                                                        ((colname ::: ty) ': FilterColumns colnames cols)



type family ValidQuery (db :: Database) (q :: SelectQuery) :: Constraint where
  ValidQuery db (Select rcs t wc) = ValidWhere wc (QueryColumnsDB db (Select rcs t wc))

type family ValidWhere (wc :: WhereClause) (cols :: [Column])  :: Constraint where
  ValidWhere Nothing cols = ()
  ValidWhere (Just e) cols = ValidExpr e cols

type family ValidExpr (e :: Expression) (cols :: [Column])  :: Constraint where
  ValidExpr Lit cols = ()
  ValidExpr (Col c) cols = ValidCol c cols

type family ValidCol (c :: ColumnName) (cols :: [Column])  :: Constraint where
  ValidCol c '[] = TypeError (Text "Column " :<>: ShowType c :<>: Text " missing")
  ValidCol c ((c ::: _) ': _) = ()
  ValidCol c (_ ': cols) = ValidCol c cols



type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)

class g (f x) => (g `O` f) x
instance g (f x) => (g `O` f) x


type family ColumnType c where
  ColumnType (_ ::: ty) = ty

class Show (ColumnType c) => ShowColumn (c :: Column)
instance Show (ColumnType c) => ShowColumn (c :: Column)

data Record (cols :: [Column]) where
  Nil  :: Record '[]
  Cons :: a -> Record cols -> Record ((colname ::: a) ': cols)
deriving instance All ShowColumn cols => Show (Record cols)

newtype Db (db :: Database) a = Db { runDb :: a }
  deriving Show

select :: forall db q . ValidQuery db q => Sing SelectQuery q -> Db db [Record (QueryColumnsDB db q)]
select s = error (toQuery s)



type ExampleQuery = Select '[ Expr (Col "name") {- AS -} (Just "foo")
                            , Expr Lit Nothing
                            , Star
                            ]
                            (LeftJoinUsing (From "users") (From "posts") '["user_id"])
                   {- WHERE -} (Just (Col "foo"))

e :: Sing SelectQuery ExampleQuery
e = Select_ (Expr_ (Col_ #name) (Just_ #foo) :> Expr_ (Lit_ 5) Nothing_ :> Star_ :> Nil_)
            (LeftJoinUsing_ (From_ #users) (From_ #posts) (#user_id :> Nil_))
            (Just_ (Col_ #foo))

type MySchema = '[ "users" := '[ "user_id" ::: Int
                               , "name"    ::: String
                               ]
                 , "posts" := '[ "post_id" ::: Int
                               , "user_id" ::: Int
                               , "message" ::: String
                               ]
                 ]

type Example = QueryColumnsDB MySchema ExampleQuery

blah = select @MySchema e
