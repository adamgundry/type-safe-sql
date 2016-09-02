{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors -Wno-unused-imports -Wno-name-shadowing #-}

module TypeSafeSQL where

import qualified Data.ByteString as BS
import qualified Database.PostgreSQL.Simple as PG
import qualified Database.PostgreSQL.Simple.FromRow as PG
import qualified Database.PostgreSQL.Simple.FromField as PG
import qualified Database.PostgreSQL.Simple.ToRow as PG
import qualified Database.PostgreSQL.Simple.ToField as PG

import Data.Kind (Type, Constraint)
import Data.String
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels
import GHC.TypeLits
import Unsafe.Coerce


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
data Expression   = Param Symbol Type | IntLit Nat | StrLit Symbol | Col ColumnName | QualCol TableName ColumnName | Equal Expression Expression


type family Params (q :: k) :: [Column] where
  Params '[]                  = '[]
  Params (x:xs)               = Params x ++ Params xs
  Params Nothing              = '[]
  Params (Just x)             = Params x
  Params (Select rcs te mb_w) = Params rcs ++ Params te ++ Params mb_w
  Params (From _)             = '[]
  Params (Join te1 te2 j)     = Params te1 ++ Params te2 ++ Params j
  Params (As te _)            = Params te
  Params Cross                = '[]
  Params (On e)               = Params e
  Params (Using _)            = '[]
  Params Star                 = '[]
  Params (Expr e _)           = Params e
  Params (Param s ty)         = '[s ::: ty]
  Params (IntLit _)           = '[]
  Params (StrLit _)           = '[]
  Params (Col _)              = '[]
  Params (QualCol _ _)        = '[]
  Params (Equal e1 e2)        = Params e1 ++ Params e2



stringToSymbol :: String -> Symbol
stringToSymbol = unsafeCoerce

symbolToString :: Symbol -> String
symbolToString = unsafeCoerce

integerToNat :: Integer -> Nat
integerToNat = unsafeCoerce

natToInteger :: Nat -> Integer
natToInteger = unsafeCoerce


class ToQuery q where
  toQuery :: q -> String

maybeToQuery :: ToQuery k => String -> Maybe k -> String
maybeToQuery _ Nothing = ""
maybeToQuery s (Just x) = " " ++ s ++ " " ++ toQuery x

instance ToQuery a => ToQuery [a] where
  toQuery [] = ""
  toQuery [x] = toQuery x
  toQuery (x:xs) = toQuery x ++ ", " ++ toQuery xs

instance ToQuery Symbol where
  toQuery = symbolToString

instance ToQuery SelectQuery where
  toQuery (Select rcs te mb_w) = "SELECT " ++ toQuery rcs ++ " FROM " ++ toQuery te ++ maybeToQuery "WHERE" mb_w

instance ToQuery TableExpr where
  toQuery (From t) = toQuery t
  toQuery (Join te1 te2 j) = case j of
    Cross      -> toQuery te1 ++ " CROSS JOIN "      ++ toQuery te2
    On e       -> toQuery te1 ++ " LEFT OUTER JOIN " ++ toQuery te2 ++ " ON " ++ toQuery e
    Using cols -> toQuery te1 ++ " LEFT OUTER JOIN " ++ toQuery te2 ++ " USING (" ++ toQuery cols ++ ")"
  toQuery (As te t) = toQuery te ++ " AS " ++ toQuery t

instance ToQuery ResultColumn where
  toQuery Star = "*"
  toQuery (Expr e mb_a) = toQuery e ++ maybeToQuery "AS" mb_a

instance ToQuery Expression where
  toQuery (Param _ _)   = "?"
  toQuery (IntLit i)    = show (natToInteger i)
  toQuery (StrLit s)    = "'" ++ symbolToString s ++ "'"
  toQuery (Col c)       = toQuery c
  toQuery (QualCol t c) = toQuery t ++ "." ++ toQuery c
  toQuery (Equal e1 e2) = toQuery e1 ++ " = " ++ toQuery e2


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
data instance Sing Nat n where
  Nat :: KnownNat n => Proxy# n -> Sing Nat n
data instance Sing Type ty where
  Type_ :: Type -> Sing Type ty

instance (s ~ x, KnownSymbol s) => IsLabel x (Sing Symbol s) where
  fromLabel = Symbol


-- Singletons for schema

data instance Sing Table t where
  (:==) :: Sing TableName tname -> Sing [Column] cols -> Sing Table (tname := cols)
data instance Sing Column x where
  Column_ :: Sing ColumnName colname -> Sing Column (colname ::: ty)


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
  Param_   :: Sing Symbol s -> Sing Type ty -> Sing Expression (Param s ty)
  IntLit_  :: Sing Nat i -> Sing Expression (IntLit i)
  StrLit_  :: Sing Symbol s -> Sing Expression (StrLit s)
  Col_     :: Sing ColumnName c -> Sing Expression (Col c)
  QualCol_ :: Sing TableName t -> Sing ColumnName c -> Sing Expression (QualCol t c)
  Equal_   :: Sing Expression e1 -> Sing Expression e2 -> Sing Expression (Equal e1 e2)


-- Implicit singletons

class SingI k (x :: k) where
  sing :: Sing k x

newtype T k (x :: k) t = MkT (SingI k x => t)

withSing :: forall k x t . Sing k x -> (SingI k x => t) -> t
withSing d f = unsafeCoerce (MkT @k @x @t f) d

instance SingI [k] '[] where
  sing = Nil_

instance (SingI k x, SingI [k] xs) => SingI [k] (x ': xs) where
  sing = sing :> sing

instance KnownSymbol s => SingI Symbol s where
  sing = Symbol proxy#

instance KnownNat n => SingI Nat n where
  sing = Nat proxy#

instance (SingI ColumnName colname) => SingI Column (colname ::: ty) where
  sing = Column_ sing


-- Converting singleton queries back to strings

class Demote k where
  demote :: Sing k e -> k

instance Demote Symbol where
  demote (Symbol p) = stringToSymbol (symbolVal' p)

instance Demote Nat where
  demote (Nat p) = integerToNat (natVal' p)

instance Demote Type where
  demote (Type_ t) = t

instance Demote k => Demote (Maybe k) where
  demote Nothing_ = Nothing
  demote (Just_ x) = Just (demote x)

instance Demote k => Demote [k] where
  demote Nil_        = []
  demote (x :> xs)   = demote x : demote xs

instance Demote SelectQuery where
  demote (Select_ rcs t mb_w) = Select (demote rcs) (demote t) (demote mb_w)

instance Demote TableExpr where
  demote (From_ t) = From (demote t)
  demote (Join_ te1 te2 j) = Join (demote te1) (demote te2) (demote j)
  demote (As_ te t) = As (demote te) (demote t)

instance Demote JoinType where
  demote Cross_ = Cross
  demote (On_ e) = On (demote e)
  demote (Using_ cols) = Using (demote cols)

instance Demote ResultColumn where
  demote Star_ = Star -- "*"
  demote (Expr_ e mb_a) = Expr (demote e) (demote mb_a)

instance Demote Expression where
  demote (Param_ s ty) = Param (demote s) (demote ty)
  demote (IntLit_ k) = IntLit (demote k)
  demote (StrLit_ s) = StrLit (demote s)
  demote (Col_ c)    = Col (demote c)
  demote (QualCol_ t c) = QualCol (demote t) (demote c)
  demote (Equal_ e1 e2) = Equal (demote e1) (demote e2)



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

-- We ought to pass table names around more here, so we can properly
-- support duplicate column names across multiple tables.

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
  ExprName (Param _ _)   = "" -- ?
  ExprName (IntLit _)    = "" -- ?
  ExprName (StrLit _)    = "" -- ?
  ExprName (Col c)       = c
  ExprName (QualCol _ c) = c

type family ExprType e cols where
  ExprType (Param _ ty)  _     = ty
  ExprType (IntLit _)    _     = Int
  ExprType (StrLit _)    _     = String
  ExprType (Col c)       cols  = LookupColumn c cols
  ExprType (QualCol _ c) cols  = LookupColumn c cols -- TODO
  ExprType (Equal e1 e2) _     = Bool

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
  ValidExpr (Param _ _) _ = ()
  ValidExpr (IntLit _)  _ = ()
  ValidExpr (StrLit _)  _ = ()
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

type family AllColumnTypes (c :: Type -> Constraint) (xs :: [Column]) :: Constraint where
  AllColumnTypes c '[] = ()
  AllColumnTypes c ((_ ::: ty) ': xs) = (c ty, AllColumnTypes c xs)

type family ColumnType c where
  ColumnType (_ ::: ty) = ty

class Show (ColumnType c) => ShowColumn (c :: Column)
instance Show (ColumnType c) => ShowColumn (c :: Column)

data Record (cols :: [Column]) where
  Nil  :: Record '[]
  Cons :: a -> Record cols -> Record ((colname ::: a) ': cols)
deriving instance AllColumnTypes Show cols => Show (Record cols)

instance (SingI [Column] cols, AllColumnTypes PG.FromField cols) => PG.FromRow (Record cols) where
  fromRow = case sing :: Sing [Column] cols of
              Nil_            -> pure Nil
              Column_ _ :> xs -> Cons <$> PG.field <*> withSing xs PG.fromRow

instance AllColumnTypes PG.ToField cols => PG.ToRow (Record cols) where
  toRow Nil = []
  toRow (Cons x xs) = PG.toField x : PG.toRow xs


-- Fake wrapper monad for issuing queries

newtype Db (db :: Database) a = Db { unDb :: PG.Connection -> IO a }

runDb :: Db db a -> IO a
runDb db = do conn <- PG.connectPostgreSQL "host='localhost' dbname='mydatabase' password='womblewomble'"
              unDb db conn <* PG.close conn

select :: forall db q cols . ( ValidQuery db q
                             , cols ~ QueryColumnsDB db q
                             , AllColumnTypes PG.FromField cols
                             , AllColumnTypes Show (Params q)
                             , AllColumnTypes PG.ToField (Params q)
                             , SingI [Column] cols)
            => Sing SelectQuery q -> Record (Params q) -> Db db [Record (QueryColumnsDB db q)]
select s p = Db $ \ conn -> do let q = toQuery (demote s)
                               print q
                               print p
                               PG.query conn (fromString q) p



-- Examples

e0 = Select_ (Star_ :> Nil_) (From_ #users) Nothing_

type ExampleQuery = Select '[ Expr (Col "name") {- AS -} (Just "foo")
                            , Expr (IntLit 5) Nothing
                            , Star
                            ]
                            (Join (From "users") (From "posts") (Using '["user_id"]))
                   {- WHERE -} (Just (Col "name" `Equal` StrLit "moo"))

e1 :: Sing SelectQuery ExampleQuery
e1 = Select_ (Expr_ (Col_ #name) (Just_ #foo) :> Expr_ (IntLit_ sing) Nothing_ :> Star_ :> Nil_)
            (Join_ (From_ #users) (From_ #posts) (Using_ (#user_id :> Nil_)))
            (Just_ (Col_ #name `Equal_` StrLit_ #moo))

e2 = Select_ (Star_ :> Nil_)
             (Join_ (From_ #posts) (From_ #users `As_` #blah)
                    (On_ (QualCol_ #blah #user_id `Equal_` QualCol_ #posts #user_id)))
             Nothing_

e3 = Select_ (Expr_ (QualCol_ #foo #baf) Nothing_ :> Nil_)
             (Join_ (From_ #users `As_` #bar) (From_ #posts `As_` #foo) Cross_)
             Nothing_

e4 = Select_ (Star_ :> Nil_) (From_ #users) (Just_ (Col_ #name `Equal_` Param_ #name undefined))

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


go e p = runDb (select @MySchema e p)

main :: IO ()
main = do print =<< go e0 Nil
          print =<< go e1 Nil
          print =<< go e2 Nil
          print =<< go e3 Nil
          print =<< go e4 (Cons "adam" Nil)
