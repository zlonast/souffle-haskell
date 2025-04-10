-- | This module exposes a uniform interface to marshal values
--   to and from Souffle Datalog. This is done via the 'Marshal' typeclass.
--   Also, a mechanism is exposed for generically deriving marshalling
--   and unmarshalling code for simple product types.
module Language.Souffle.Marshal
  ( Marshal(..)
  , MonadPush(..)
  , MonadPop(..)
  , SimpleProduct
  ) where

import           Control.Applicative (Applicative (..))
import           Control.Monad       (Monad)

import           Data.Function       ((.))
import           Data.Functor        ((<$>))
import           Data.Int            (Int32)
import           Data.Kind           (Constraint, Type)
import           Data.String         (String)
import qualified Data.Text           as T
import qualified Data.Text.Lazy      as TL
import           Data.Word           (Word32)

import           GHC.Classes         (CTuple2, CUnit)
import           GHC.Float           (Float)
import           GHC.Generics        (Generic (..), K1 (..), M1 (..), U1, V1, type (:*:) (..), type (:+:))
import           GHC.Tuple           (Unit)
import           GHC.TypeLits        (ErrorMessage (..), TypeError)

{- | A typeclass for serializing primitive values from Haskell to Datalog.

This typeclass is only used internally and subject to change.

See also: 'MonadPop', 'Marshal'.
-}
type MonadPush :: (Type -> Type) -> Constraint
class Monad m => MonadPush m where
  -- | Marshals a signed 32 bit integer to the datalog side.
  pushInt32 :: Int32 -> m Unit
  -- | Marshals an unsigned 32 bit integer to the datalog side.
  pushUInt32 :: Word32 -> m Unit
  -- | Marshals a float to the datalog side.
  pushFloat :: Float -> m Unit
  -- | Marshals a string to the datalog side.
  pushString :: String -> m Unit
  -- | Marshals a UTF8-encoded Text string to the datalog side.
  pushText :: T.Text -> m Unit

{- | A typeclass for serializing primitive values from Datalog to Haskell.

This typeclass is only used internally and subject to change.

See also: 'MonadPush', 'Marshal'.
-}
type MonadPop :: (Type -> Type) -> Constraint
class Monad m => MonadPop m where
  -- | Unmarshals a signed 32 bit integer from the datalog side.
  popInt32 :: m Int32
  -- | Unmarshals an unsigned 32 bit integer from the datalog side.
  popUInt32 :: m Word32
  -- | Unmarshals a float from the datalog side.
  popFloat :: m Float
  -- | Unmarshals a string from the datalog side.
  popString :: m String
  -- | Unmarshals a UTF8-encoded Text string from the datalog side.
  popText :: m T.Text

{- | A typeclass for providing a uniform API to marshal/unmarshal values
     between Haskell and Souffle datalog.

The marshalling is done via a stack-based approach, where elements are
pushed/popped one by one. You need to make sure that the marshalling
of values happens in the correct order or unexpected things might happen
(including crashes). Pushing and popping of fields should happen in the
same order (from left to right, as defined in Datalog). The ordering of how
nested products are serialized is the same as when the fields of the nested
product types are inlined into the parent type.

Generic implementations for 'push' and 'pop' that perform the previously
described behavior are available. This makes it possible to
write very succinct code:

@
data Edge = Edge String String deriving Generic

instance Marshal Edge
@
-}
type Marshal :: Type -> Constraint
class Marshal a where
  -- | Marshals a value to the datalog side.
  push :: MonadPush m => a -> m Unit
  -- | Unmarshals a value from the datalog side.
  pop :: MonadPop m => m a

  default push
    :: (Generic a, SimpleProduct a, GMarshal (Rep a), MonadPush m)
    => a -> m Unit
  default pop
    :: (Generic a, SimpleProduct a, GMarshal (Rep a), MonadPop m)
    => m a
  push a = gpush (from a)
  {-# INLINABLE push #-}

  pop = to <$> gpop
  {-# INLINABLE pop #-}

instance Marshal Int32 where
  push :: MonadPush m => Int32 -> m Unit
  push = pushInt32
  {-# INLINABLE push #-}

  pop :: MonadPop m => m Int32
  pop = popInt32
  {-# INLINABLE pop #-}

instance Marshal Word32 where
  push :: MonadPush m => Word32 -> m Unit
  push = pushUInt32
  {-# INLINABLE push #-}

  pop :: MonadPop m => m Word32
  pop = popUInt32
  {-# INLINABLE pop #-}

instance Marshal Float where
  push :: MonadPush m => Float -> m Unit
  push = pushFloat
  {-# INLINABLE push #-}

  pop :: MonadPop m => m Float
  pop = popFloat
  {-# INLINABLE pop #-}

instance Marshal String where
  push :: MonadPush m => String -> m Unit
  push = pushString
  {-# INLINABLE push #-}

  pop :: MonadPop m => m String
  pop = popString
  {-# INLINABLE pop #-}

instance Marshal T.Text where
  push :: MonadPush m => T.Text -> m Unit
  push = pushText
  {-# INLINABLE push #-}

  pop :: MonadPop m => m T.Text
  pop = popText
  {-# INLINABLE pop #-}

instance Marshal TL.Text where
  push :: MonadPush m => TL.Text -> m Unit
  push = push . TL.toStrict
  {-# INLINABLE push #-}

  pop :: MonadPop m => m TL.Text
  pop = TL.fromStrict <$> pop
  {-# INLINABLE pop #-}

type GMarshal :: (Type -> Type) -> Constraint
class GMarshal f where
  gpush :: MonadPush m => f a -> m Unit
  gpop  :: MonadPop m => m (f a)

instance Marshal a => GMarshal (K1 i a) where
  gpush :: (Marshal a, MonadPush m) => K1 i a a1 -> m Unit
  gpush (K1 x) = push x
  {-# INLINABLE gpush #-}

  gpop :: (Marshal a, MonadPop m) => m (K1 i a a1)
  gpop = K1 <$> pop
  {-# INLINABLE gpop #-}

instance (GMarshal f, GMarshal g) => GMarshal (f :*: g) where
  gpush :: (GMarshal f, GMarshal g, MonadPush m) => (:*:) f g a -> m Unit
  gpush (a :*: b) = do
    gpush a
    gpush b
  {-# INLINABLE gpush #-}

  gpop :: (GMarshal f, GMarshal g, MonadPop m) => m ((:*:) f g a)
  gpop = (:*:) <$> gpop <*> gpop
  {-# INLINABLE gpop #-}

instance GMarshal a => GMarshal (M1 i c a) where
  gpush :: (GMarshal a, MonadPush m) => M1 i c a a1 -> m Unit
  gpush (M1 x) = gpush x
  {-# INLINABLE gpush #-}

  gpop :: (GMarshal a, MonadPop m) => m (M1 i c a a1)
  gpop = M1 <$> gpop
  {-# INLINABLE gpop #-}


-- | A helper type family used for generating a more user-friendly type error
--   for incompatible types when generically deriving marshalling code for
--   the 'Language.Souffle.Marshal.Marshal' typeclass.
--
--   The __a__ type parameter is the original type, used when displaying the type error.
--
--   A type error is returned if the passed in type is not a simple product type
--   consisting of only types that implement 'Marshal'.
type SimpleProduct :: Type -> Constraint
type family SimpleProduct a where
  SimpleProduct a = CTuple2 (ProductLike a (Rep a)) (OnlyMarshallableFields (Rep a))

type ProductLike :: Type -> (Type -> Type) -> Constraint
type family ProductLike t f where
  ProductLike t (a :*: b)  = CTuple2 (ProductLike t a) (ProductLike t b)
  ProductLike t (M1 _ _ a) = ProductLike t a
  ProductLike _ (K1 _ _)   = CUnit
  ProductLike t (_ :+: _)  =
    TypeError ( 'Text "Error while deriving marshalling code for type " ':<>: 'ShowType t ':<>: 'Text ":"
              ':$$: 'Text "Cannot derive sum type, only product types are supported.")
  ProductLike t U1 =
    TypeError ( 'Text "Error while deriving marshalling code for type " ':<>: 'ShowType t ':<>: 'Text ":"
              ':$$: 'Text "Cannot automatically derive code for 0 argument constructor.")
  ProductLike t V1 =
    TypeError ( 'Text "Error while deriving marshalling code for type " ':<>: 'ShowType t ':<>: 'Text ":"
              ':$$: 'Text "Cannot derive void type.")

type OnlyMarshallableFields :: (Type -> Type) -> Constraint
type family OnlyMarshallableFields f where
  OnlyMarshallableFields (a :*: b)  = CTuple2 (OnlyMarshallableFields a) (OnlyMarshallableFields b)
  OnlyMarshallableFields (a :+: b)  = CTuple2 (OnlyMarshallableFields a) (OnlyMarshallableFields b)
  OnlyMarshallableFields (M1 _ _ a) = OnlyMarshallableFields a
  OnlyMarshallableFields U1         = CUnit
  OnlyMarshallableFields V1         = CUnit
  OnlyMarshallableFields k          = OnlyMarshallableField k

type OnlyMarshallableField :: (Type -> Type) -> Constraint
type family OnlyMarshallableField f where
  OnlyMarshallableField (M1 _ _ a) = OnlyMarshallableField a
  OnlyMarshallableField (K1 _ a)   = Marshal a
