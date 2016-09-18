{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors -Wno-unused-imports -Wno-name-shadowing #-}

module TypeSafeSQL where

import qualified Data.ByteString as BS
import qualified Data.Singletons as S
import qualified Data.Singletons.TH as S
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


stringToSymbol :: String -> Symbol
stringToSymbol = unsafeCoerce

symbolToString :: Symbol -> String
symbolToString = unsafeCoerce

integerToNat :: Integer -> Nat
integerToNat = unsafeCoerce

natToInteger :: Nat -> Integer
natToInteger = unsafeCoerce


newtype TableName = T Symbol

{-
newtype ColumnName = C Symbol
newtype StrSymbol = S Symbol
newtype ParamName = P Symbol
-}

type ColumnName = TableName
type StrSymbol = TableName
type ParamName = TableName

type C = T
type S = T
type P = T

data instance S.Sing (t :: TableName) where
  STableName :: S.Sing s -> S.Sing (T s)

instance KnownSymbol s => S.SingI (T s) where
  sing = STableName S.sing

instance S.SingKind TableName where
  type DemoteRep TableName = TableName

  fromSing :: S.Sing (a :: TableName) -> S.DemoteRep TableName
  fromSing (STableName s) = T (stringToSymbol (S.fromSing s))
  toSing (T s) = case someSymbolVal (symbolToString s) of
                   SomeSymbol (_ :: S.Proxy t) -> S.SomeSing (STableName (S.sing :: S.Sing t))


data instance S.Sing (a :: Type) where
  SType :: Type -> S.Sing (a :: Type)

instance S.SingKind Type where
  type DemoteRep Type = Type
  fromSing (SType t) = t
  toSing t = S.SomeSing (SType t)


data IntegerLit = Pos Nat
                | Neg Nat

instance Eq   IntegerLit where
  x == y = toInteger x == toInteger y

instance Ord  IntegerLit
instance Num  IntegerLit
instance Real IntegerLit
instance Enum IntegerLit

instance Integral IntegerLit where
  toInteger (Pos n) = natToInteger n
  toInteger (Neg n) = - natToInteger n

data instance S.Sing (i :: IntegerLit) where
  SPos :: S.Sing n -> S.Sing (Pos n)
  SNeg :: S.Sing n -> S.Sing (Neg n)

instance S.SingKind IntegerLit where
  type DemoteRep IntegerLit = IntegerLit
  fromSing (SPos n) = Pos (integerToNat (S.fromSing n))
  fromSing (SNeg n) = Neg (integerToNat (S.fromSing n))
  toSing (Pos n) = case someNatVal (natToInteger n) of
                     Just (SomeNat (_ :: S.Proxy n)) -> S.SomeSing (SPos (S.sing :: S.Sing n))
                     Nothing -> error "erk"
  toSing (Neg n) = case someNatVal (natToInteger n) of
                     Just (SomeNat (_ :: S.Proxy n)) -> S.SomeSing (SNeg (S.sing :: S.Sing n))
                     Nothing -> error "erk"

instance KnownNat n => S.SingI (Pos n) where
  sing = SPos S.sing

instance KnownNat n => S.SingI (Neg n) where
  sing = SNeg S.sing


$(S.singletons [d|

  -- Schema representation
  data Table      = TableName := [Column]
  data Column     = ColumnName ::: Type

  -- Syntax of queries at type level
  data Expression   = Param ParamName Type
                    | IntLit IntegerLit
                    | StrLit StrSymbol
                    | Col ColumnName
                    | QualCol TableName ColumnName
                    | Equal Expression Expression

  data JoinType = Cross | On Expression | Using [ColumnName]
  data TableExpr = From TableName
                 | Join TableExpr TableExpr JoinType
                 | As TableExpr TableName
 |])

type CrossJoin te1 te2 = Join te1 te2 Cross
type WhereClause  = Maybe Expression
type AsClause     = Maybe ColumnName

$(S.singletons [d|
  data SelectQuery = Select [ResultColumn] TableExpr WhereClause
  data ResultColumn = Star | Expr Expression AsClause
 |])

type Database   = [Table]


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
  Params (Param (P s) ty)     = '[C s ::: ty]
  Params (IntLit _)           = '[]
  Params (StrLit _)           = '[]
  Params (Col _)              = '[]
  Params (QualCol _ _)        = '[]
  Params (Equal e1 e2)        = Params e1 ++ Params e2


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

instance ToQuery TableName where
  toQuery (T s) = toQuery s

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
  toQuery (IntLit i)    = show (toInteger i)
  toQuery (StrLit (T s))  = "'" ++ symbolToString s ++ "'"
  toQuery (Col c)       = toQuery c
  toQuery (QualCol t c) = toQuery t ++ "." ++ toQuery c
  toQuery (Equal e1 e2) = toQuery e1 ++ " = " ++ toQuery e2



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

type family ExprName e :: ColumnName where
  ExprName (Param _ _)   = C "" -- ?
  ExprName (IntLit _)    = C "" -- ?
  ExprName (StrLit _)    = C "" -- ?
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

instance PG.FromRow (Record '[]) where
  fromRow = pure Nil

instance (PG.FromField ty, PG.FromRow (Record cols)) => PG.FromRow (Record ((colname '::: ty) ': cols)) where
  fromRow = Cons <$> PG.field <*> PG.fromRow

instance PG.ToRow (Record '[]) where
  toRow Nil = []

instance (PG.ToField ty, PG.ToRow (Record cols)) => PG.ToRow (Record ((colname '::: ty) ': cols)) where
  toRow (Cons x xs) = PG.toField x : PG.toRow xs

-- Fake wrapper monad for issuing queries

newtype Db (db :: Database) a = Db { unDb :: PG.Connection -> IO a }

runDb :: Db db a -> IO a
runDb db = do conn <- PG.connectPostgreSQL "host='localhost' dbname='mydatabase' password='womblewomble'"
              unDb db conn <* PG.close conn

select :: forall db q cols . ( ValidQuery db q
                             , cols ~ QueryColumnsDB db q
                             , PG.ToRow (Record (Params q))
                             , PG.FromRow (Record cols)
                             , Show (Record (Params q))
                             , S.SingI q
                             )
            => Record (Params q) -> Db db [Record (QueryColumnsDB db q)]
select p = Db $ \ conn -> do let q = toQuery (S.fromSing (S.sing :: S.Sing q))
                             print q
                             print p
                             PG.query conn (fromString q) p



-- Examples

type E0 = Select '[Star] (From (T "users")) Nothing
-- e0 = Select_ (Star_ :> Nil_) (From_ #users) Nothing_

type E1 = Select '[ Expr (Col (C "name")) {- AS -} (Just (C "foo"))
                            , Expr (IntLit (Pos 5)) Nothing
                            , Star
                            ]
                            (Join (From (T "users")) (From (T "posts")) (Using '[C "user_id"]))
                   {- WHERE -} (Just (Col (C "name") `Equal` StrLit (S "moo")))
{-
e1 :: Sing SelectQuery E1
e1 = Select_ (Expr_ (Col_ #name) (Just_ #foo) :> Expr_ (IntLit_ sing) Nothing_ :> Star_ :> Nil_)
            (Join_ (From_ #users) (From_ #posts) (Using_ (#user_id :> Nil_)))
            (Just_ (Col_ #name `Equal_` StrLit_ #moo))
-}

type E2 = Select '[Star] (Join (From (T "posts")) (From (T "users") `As` T "blah") (On (QualCol (T "blah") (C "user_id") `Equal` QualCol (T "posts") (C "user_id")))) Nothing
{-
e2 = Select_ (Star_ :> Nil_)
             (Join_ (From_ #posts) (From_ #users `As_` #blah)
                    (On_ (QualCol_ #blah #user_id `Equal_` QualCol_ #posts #user_id)))
             Nothing_
-}

type E3 = Select '[Expr (QualCol (T "foo") (C "baf")) Nothing]
                 ((From (T "users") `As` T "bar") `CrossJoin` (From (T "posts") `As` T "foo"))
                 Nothing
{-
e3 = Select_ (Expr_ (QualCol_ #foo #baf) Nothing_ :> Nil_)
             (Join_ (From_ #users `As_` #bar) (From_ #posts `As_` #foo) Cross_)
             Nothing_
-}

-- type E4 = Select '[Star] (From (T "users")) (Just (Col (C "name") `Equal` Param (P "name") String))
-- e4 = Select_ (Star_ :> Nil_) (From_ #users) (Just_ (Col_ #name `Equal_` Param_ #name undefined))

type MySchema = '[ T "users" := '[ C "user_id" ::: Int
                                 , C "name"    ::: String
                                 , C "baf"     ::: Bool
                                 ]
                 , T "posts" := '[ C "post_id" ::: Int
                                 , C "user_id" ::: Int
                                 , C "message" ::: String
                                 , C "baf"     ::: Int
                                 ]
                 ]

go :: forall q cols . ( ValidQuery MySchema q
                      , cols ~ QueryColumnsDB MySchema q
                      , PG.ToRow (Record (Params q))
                      , PG.FromRow (Record cols)
                      , Show (Record (Params q))
                      , S.SingI q
                      )
        => Record (Params q) -> IO [Record (QueryColumnsDB MySchema q)]
go p = runDb (select @MySchema @q p)

main :: IO ()
main = do print =<< go @E0 Nil
          print =<< go @E1 Nil
          print =<< go @E2 Nil
          print =<< go @E3 Nil
--           print =<< go @E4 (Cons "adam" Nil)
