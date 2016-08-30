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
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors -Wno-unused-imports -Wno-name-shadowing #-}

module TypeSafeSQL where

import Data.Kind (Type, Constraint)
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels
import GHC.TypeLits


-- Schema representation

type Database   = [Table]
data Table      = TableName := [Column]
data Column     = ColumnName ::: Type
type TableName  = Symbol
type ColumnName = Symbol


-- Syntax of queries at type level

data SelectQuery = Select [ResultColumn] TableExpr WhereClause

data TableExpr = From TableName
               | Join TableExpr TableExpr JoinType
               | As TableExpr TableName
data JoinType = Cross | On Expression | Using [ColumnName]

data ResultColumn = Star | Expr Expression AsClause

type WhereClause  = Maybe Expression
type AsClause     = Maybe ColumnName
data Expression   = IntLit | StrLit | Col ColumnName | QualCol TableName ColumnName | Equal Expression Expression


-- General-purpose singletons

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

instance (s ~ x, KnownSymbol s) => IsLabel x (Sing Symbol s) where
  fromLabel = Symbol


-- Singletons for representing queries at value level

data instance Sing SelectQuery q where
  Select_ :: Sing [ResultColumn] rcs -> Sing TableExpr te -> Sing WhereClause wc
          -> Sing SelectQuery (Select rcs te wc)
data instance Sing ResultColumn rc where
  Star_ :: Sing ResultColumn Star
  Expr_ :: Sing Expression e -> Sing AsClause a -> Sing ResultColumn (Expr e a)
data instance Sing TableExpr te where
  From_ :: Sing TableName t -> Sing TableExpr (From t)
  Join_ :: Sing TableExpr te1 -> Sing TableExpr te2 -> Sing JoinType j -> Sing TableExpr (Join te1 te2 j)
  As_ :: Sing TableExpr te -> Sing TableName t -> Sing TableExpr (As te t)
data instance Sing JoinType j where
  Cross_ :: Sing JoinType Cross
  On_    :: Sing Expression e -> Sing JoinType (On e)
  Using_ :: Sing [ColumnName] cols -> Sing JoinType (Using cols)
data instance Sing Expression e where
  IntLit_  :: Int -> Sing Expression IntLit
  StrLit_  :: String -> Sing Expression StrLit
  Col_     :: Sing ColumnName c -> Sing Expression (Col c)
  QualCol_ :: Sing TableName t -> Sing ColumnName c -> Sing Expression (QualCol t c)
  Equal_   :: Sing Expression e1 -> Sing Expression e2 -> Sing Expression (Equal e1 e2)


-- Converting singleton queries back to strings
-- (perhaps this should go to simply 'k'?)

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
  toQuery (Join_ te1 te2 j) = case j of
    Cross_      -> toQuery te1 ++ " CROSS JOIN "      ++ toQuery te2
    On_ e       -> toQuery te1 ++ " LEFT OUTER JOIN " ++ toQuery te2 ++ " ON " ++ toQuery e
    Using_ cols -> toQuery te1 ++ " LEFT OUTER JOIN " ++ toQuery te2 ++ " USING " ++ toQuery cols
  toQuery (As_ te t) = toQuery te ++ " AS " ++ toQuery t

instance ToQuery ResultColumn where
  toQuery Star_ = "*"
  toQuery (Expr_ e mb_a) = toQuery e ++ maybeToQuery "AS" mb_a

instance ToQuery Expression where
  toQuery (IntLit_ k) = show k
  toQuery (StrLit_ s) = show s
  toQuery (Col_ c)    = toQuery c
  toQuery (QualCol_ t c) = toQuery t ++ "." ++ toQuery c
  toQuery (Equal_ e1 e2) = toQuery e1 ++ " == " ++ toQuery e2



-- Misc type family utilities

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

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)

class g (f x) => (g `O` f) x
instance g (f x) => (g `O` f) x


-- Calculating the result columns for queries

type family QueryColumnsDB (db :: Database) (q :: SelectQuery) :: [Column] where
  QueryColumnsDB db (Select rcs te _wc) = LookupResultColumns rcs (ExpandTableExpr db te)

type family ExpandTableExpr (db :: Database) (te :: TableExpr) :: [Column] where
  ExpandTableExpr db (From t) = LookupTable t db
  ExpandTableExpr db (Join te1 te2 (Using cols)) = LookupColumns cols (ExpandTableExpr db te1)
                                                ++ FilterColumns cols (ExpandTableExpr db te1)
                                                ++ FilterColumns cols (ExpandTableExpr db te2)
  ExpandTableExpr db (Join te1 te2 _) = ExpandTableExpr db te1 ++ ExpandTableExpr db te2
  ExpandTableExpr db (As te t) = ExpandTableExpr db te -- TODO

type family LookupResultColumns (rcs :: [ResultColumn]) (cols :: [Column]) :: [Column] where
  LookupResultColumns '[] cols = '[]
  LookupResultColumns (Star ': rcs) cols = cols
  LookupResultColumns ('Expr e Nothing  ': rcs) cols = (ExprName e ::: ExprType e cols) ': LookupResultColumns rcs cols
  LookupResultColumns ('Expr e (Just c) ': rcs) cols = (c ::: ExprType e cols) ': LookupResultColumns rcs cols

type family ExprName e where
  ExprName IntLit = "" -- ?
  ExprName StrLit = "" -- ?
  ExprName (Col c) = c
  ExprName (QualCol _ c) = c

type family ExprType e cols where
  ExprType IntLit  _     = Int
  ExprType StrLit  _     = String
  ExprType (Col c) cols  = LookupColumn c cols
  ExprType (QualCol _ c) cols = LookupColumn c cols -- TODO
  ExprType (Equal e1 e2) _ = Bool

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


-- Checking validity of queries

type family ValidQuery (db :: Database) (q :: SelectQuery) :: Constraint where
  ValidQuery db (Select rcs t wc) = (ValidTableExpr db t, ValidWhere wc (QueryColumnsDB db (Select rcs t wc)))

type family ValidTableExpr db t where
  ValidTableExpr db (From t) = ValidTableName t db
  ValidTableExpr db (Join te1 te2 j) = (ValidTableExpr db te1, ValidTableExpr db te2, ValidJoin db te1 te2 j)
  ValidTableExpr db (As te t) = ValidTableExpr db te

type family ValidJoin db te1 te2 j :: Constraint where
  ValidJoin db te1 te2 Cross        = ()
  ValidJoin db te1 te2 (On e)       = ExprType e (ExpandTableExpr db (Join te1 te2 (On e))) ~ Bool
  ValidJoin db te1 te2 (Using cols) = (ValidCols cols (ExpandTableExpr db te1), ValidCols cols (ExpandTableExpr db te2))

type family ValidWhere (wc :: WhereClause) (cols :: [Column])  :: Constraint where
  ValidWhere Nothing cols = ()
  ValidWhere (Just e) cols = ValidExpr e cols

type family ValidExpr (e :: Expression) (cols :: [Column])  :: Constraint where
  ValidExpr IntLit  _ = ()
  ValidExpr StrLit  _ = ()
  ValidExpr (Col c) cols = ValidCol c cols
  ValidExpr (QualCol _ c) cols = ValidCol c cols -- TODO
  ValidExpr (Equal e1 e2) cols = (ValidExpr e1 cols, ValidExpr e2 cols, ExprType e1 cols ~ ExprType e2 cols)

type family ValidCols (colnames :: [ColumnName]) (cols :: [Column]) :: Constraint where
  ValidCols '[] cols = ()
  ValidCols (colname ': colnames) cols = (ValidCol colname cols, ValidCols colnames cols)

type family ValidCol (c :: ColumnName) (cols :: [Column])  :: Constraint where
  ValidCol c '[] = TypeError (Text "Column " :<>: ShowType c :<>: Text " missing")
  ValidCol c ((c ::: _) ': _) = ()
  ValidCol c (_ ': cols) = ValidCol c cols

type family ValidTableName (t :: TableName) (tables :: [Table])  :: Constraint where
  ValidTableName t '[] = TypeError (Text "Table " :<>: ShowType t :<>: Text " missing")
  ValidTableName t ((t := _) ': _) = ()
  ValidTableName t (_ ': tables) = ValidTableName t tables


-- Anonymous records

type family ColumnType c where
  ColumnType (_ ::: ty) = ty

class Show (ColumnType c) => ShowColumn (c :: Column)
instance Show (ColumnType c) => ShowColumn (c :: Column)

data Record (cols :: [Column]) where
  Nil  :: Record '[]
  Cons :: a -> Record cols -> Record ((colname ::: a) ': cols)
deriving instance All ShowColumn cols => Show (Record cols)


-- Fake wrapper monad for issuing queries

newtype Db (db :: Database) a = Db { runDb :: a }
  deriving Show

select :: forall db q . ValidQuery db q => Sing SelectQuery q -> Db db [Record (QueryColumnsDB db q)]
select s = error (toQuery s)



-- Examples

type ExampleQuery = Select '[ Expr (Col "name") {- AS -} (Just "foo")
                            , Expr IntLit Nothing
                            , Star
                            ]
                            (Join (From "users") (From "posts") (Using '["user_id"]))
                   {- WHERE -} (Just (Col "foo" `Equal` StrLit))

e1 :: Sing SelectQuery ExampleQuery
e1 = Select_ (Expr_ (Col_ #name) (Just_ #foo) :> Expr_ (IntLit_ 5) Nothing_ :> Star_ :> Nil_)
            (Join_ (From_ #users) (From_ #posts) (Using_ (#user_id :> Nil_)))
            (Just_ (Col_ #foo `Equal_` StrLit_ "moo"))

e2 = Select_ (Star_ :> Nil_)
             (Join_ (From_ #posts) (From_ #users `As_` #blah)
                    (On_ (QualCol_ #foo #user_id `Equal_` QualCol_ #posts #user_id)))
             Nothing_

e3 = Select_ (Expr_ (QualCol_ #foo #baf) Nothing_ :> Nil_)
             (Join_ (From_ #users `As_` #bar) (From_ #posts `As_` #foo) Cross_)
             Nothing_

type MySchema = '[ "users" := '[ "user_id" ::: Int
                               , "name"    ::: String
                               , "baf"     ::: Bool
                               ]
                 , "posts" := '[ "post_id" ::: Int
                               , "user_id" ::: Int
                               , "message" ::: String
                               , "baf"     ::: Int
                               ]
                 ]

type Example = QueryColumnsDB MySchema ExampleQuery

blah = select @MySchema e1
