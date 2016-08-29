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

module TypeSafeSQL where

import Data.Kind (Type, Constraint)
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels
import GHC.TypeLits


type Database = [Table]
type Table = (TableName, [Column])
type Column = (ColumnName, Type)

type TableName = Symbol
type ColumnName = Symbol

data TableName_ (a :: TableName) = TableName_
data ColumnName_ (a :: ColumnName) = ColumnName_

instance x ~ table => IsLabel x (TableName_ table) where
  fromLabel _ = TableName_

instance x ~ column => IsLabel x (ColumnName_ column) where
  fromLabel _ = ColumnName_

newtype Db (db :: Database) a = Db { runDb :: a }

type family QueryColumns db colnames table :: [Column] where
  QueryColumns '[] colnames table = TypeError (Text "Table " :<>: ShowType table :<>: Text " missing")
  QueryColumns ('(table, cols) ': _) colnames table = LookupColumns colnames cols
  QueryColumns (x ': db)             colnames table = QueryColumns db colnames table

type family LookupColumns colnames cols :: [Column] where
  LookupColumns '[] cols = '[]
  LookupColumns (colname ': colnames) cols = '(colname, LookupColumn colname cols) ': LookupColumns colnames cols

type family LookupColumn colname cols :: Type where
  LookupColumn colname '[] = TypeError (Text "Column " :<>: ShowType colname :<>: Text " missing")
  LookupColumn colname ('(colname, ty) ': _) = ty
  LookupColumn colname (_ ': cols) = LookupColumn colname cols


data Record (cols :: [Column]) where
  Nil  :: Record '[]
  Cons :: a -> Record cols -> Record ('(colname, a) ': cols)

data ColumnNames (cols :: [ColumnName]) = ColumnNames

instance y ~ '[x] => IsLabel x (ColumnNames y) where
  fromLabel _ = ColumnNames

(<:>) :: ColumnName_ colname -> ColumnNames cols -> ColumnNames (colname ': cols)
_ <:> _ = ColumnNames


-- select cols from :table
select0 :: ColumnNames cols -> TableName_ table -> Db db [Record (QueryColumns db cols table)]
select0 = undefined


type table := cols = '( table, cols )
type col ::: ty = '( col, ty )

type MySchema = '[ "users" := '[ "id" ::: Int
                               , "name" ::: String
                               ]
                 ]

example :: Db MySchema [Record '[ "name" ::: String, "id" ::: Int ]]
example = select0 (#name <:> #id) #users


-- SELECT [DISTINCT | ALL] result-column*
--   [FROM (table-or-subquery* | join-clause)] [WHERE expr] [GROUP BY expr* [HAVING expr]]
--   [ORDER BY ordering-term*] [LIMIT expr [OFFSET expr]]

-- result-column ::= * | expr [AS column-alias] | table-name . *


data SelectQuery = Select { resultColumns :: [ResultColumn]
                          , fromClause    :: TableName
                          , whereClause   :: WhereClause
                          }

type WhereClause = Maybe Expression
type AsClause = Maybe ColumnName
data ResultColumn = Star | Expr Expression AsClause
data Expression = Lit | Col ColumnName


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
  Select_ :: Sing [ResultColumn] rcs -> Sing TableName t -> Sing WhereClause wc
          -> Sing SelectQuery (Select rcs t wc)
data instance Sing ResultColumn rc where
  Star_ :: Sing ResultColumn Star
  Expr_ :: Sing Expression e -> Sing AsClause a -> Sing ResultColumn (Expr e a)
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

instance ToQuery ResultColumn where
  toQuery Star_ = "*"
  toQuery (Expr_ e mb_a) = toQuery e ++ maybeToQuery "AS" mb_a

instance ToQuery Expression where
  toQuery (Lit_ k) = show k
  toQuery (Col_ c) = toQuery c



type family QueryColumnsDB db q :: [Column] where
  QueryColumnsDB db (Select rcs t _wc) = LookupResultColumns rcs (LookupTable t db)

type family LookupResultColumns rcs cols :: [Column] where
  LookupResultColumns '[] cols = '[]
  LookupResultColumns (Star ': rcs) cols = cols
  LookupResultColumns ('Expr e Nothing  ': rcs) cols = '(ExprName e, ExprType e cols) ': LookupResultColumns rcs cols
  LookupResultColumns ('Expr e (Just c) ': rcs) cols = '(c, ExprType e cols) ': LookupResultColumns rcs cols

type family ExprName e where
  ExprName Lit = "" -- ?
  ExprName (Col c) = c

type family ExprType e cols where
  ExprType Lit cols = Int -- ?
  ExprType (Col c) cols = LookupColumn c cols

type family LookupTable table db :: [Column] where
  LookupTable table '[] = TypeError (Text "Table " :<>: ShowType table :<>: Text " missing")
  LookupTable table ('(table, cols) ': _) = cols
  LookupTable table (_ ': db) = LookupTable table db


type family ValidQuery db q :: Constraint where
  ValidQuery db (Select rcs t wc) = ValidWhere wc (QueryColumnsDB db (Select rcs t wc))

type family ValidWhere wc cols  :: Constraint where
  ValidWhere Nothing cols = ()
  ValidWhere (Just e) cols = ValidExpr e cols

type family ValidExpr e cols  :: Constraint where
  ValidExpr Lit cols = ()
  ValidExpr (Col c) cols = ValidCol c cols

type family ValidCol c cols  :: Constraint where
  ValidCol c '[] = TypeError (Text "Column " :<>: ShowType c :<>: Text " missing")
  ValidCol c ('(c, _) ': _) = ()
  ValidCol c (_ ': cols) = ValidCol c cols


type ExampleQuery = Select '[ Expr (Col "name") {- AS -} (Just "foo")
                            , Expr Lit Nothing
                            , Star
                            ]
                   {- FROM -} "users"
                   {- WHERE -} (Just (Col "foo"))

e :: Sing SelectQuery ExampleQuery
e = Select_ (Expr_ (Col_ #name) (Just_ #foo) :>
             Expr_ (Lit_ 5) Nothing_ :> Star_ :> Nil_) #users (Just_ (Col_ #foo))

type Example = QueryColumnsDB MySchema ExampleQuery

select :: forall db q . ValidQuery db q => Sing SelectQuery q -> Db db [Record (QueryColumnsDB db q)]
select s = error (toQuery s)
