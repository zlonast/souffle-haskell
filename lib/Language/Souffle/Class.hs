-- | This module provides the top level API for Souffle related operations.
--   It makes use of Haskell's powerful typesystem to make certain invalid states
--   impossible to represent. It does this with a small type level DSL for
--   describing properties of the Datalog program (see the 'Program' and 'Fact'
--   typeclasses for more information).
--
--   The Souffle operations are exposed via 2 mtl-style interfaces
--   (see `MonadSouffle` and `MonadSouffleFileIO`) that allows them to be
--   integrated with existing monad transformer stacks.
--
--   This module also contains some helper type families for additional
--   type safety and user-friendly error messages.
module Language.Souffle.Class
  ( Program(..)
  , ProgramOptions(..)
  , Fact(..)
  , FactOptions(..)
  , Marshal.Marshal(..)
  , Direction(..)
  , ContainsInputFact
  , ContainsOutputFact
  , ContainsFact
  , MonadSouffle(..)
  , MonadSouffleFileIO(..)
  ) where

import           Control.Monad.Except       (ExceptT)
import           Control.Monad.Reader       (MonadTrans (..), ReaderT)
import qualified Control.Monad.RWS.Lazy     as LazyRWS
import qualified Control.Monad.RWS.Strict   as StrictRWS
import qualified Control.Monad.State.Lazy   as LazyState
import qualified Control.Monad.State.Strict as StrictState
import           Control.Monad.Writer       (WriterT)

import           Data.Kind                  (Constraint, Type)
import           Data.Proxy                 (Proxy (..))
import           Data.Word                  (Word64)

import           GHC.TypeLits               (ErrorMessage (..), KnownSymbol, Symbol, TypeError, symbolVal)

import qualified Language.Souffle.Marshal   as Marshal

import           Prelude                    hiding (init)


-- | A helper type family for checking if a specific Souffle `Program` contains
--   a certain `Fact`. Additionally, it also checks if the fact is marked as
--   either `Input` or `InputOutput`. This constraint will generate a
--   user-friendly type error if these conditions are not met.
type ContainsInputFact :: Type -> Type -> Constraint
type family ContainsInputFact prog fact where
  ContainsInputFact prog fact = (ContainsFact prog fact, IsInput fact (FactDirection fact))

-- | A helper type family for checking if a specific Souffle `Program` contains
--   a certain `Fact`. Additionally, it also checks if the fact is marked as
--   either `Output` or `InputOutput`. This constraint will generate a
--   user-friendly type error if these conditions are not met.
type ContainsOutputFact :: Type -> Type -> Constraint
type family ContainsOutputFact prog fact where
  ContainsOutputFact prog fact = (ContainsFact prog fact, IsOutput fact (FactDirection fact))

type IsInput :: Type -> Direction -> Constraint
type family IsInput fact dir where
  IsInput _ 'Input = ()
  IsInput _ 'InputOutput = ()
  IsInput fact dir = TypeError
    ( 'Text "You tried to use an " ':<>: 'ShowType (FormatDirection dir) ':<>: 'Text " fact of type " ':<>: 'ShowType fact ':<>: 'Text " as an input."
    ':$$: 'Text "Possible solution: change the FactDirection of " ':<>: 'ShowType fact
      ':<>: 'Text " to either 'Input' or 'InputOutput'."
    )

type IsOutput :: Type -> Direction -> Constraint
type family IsOutput fact dir where
  IsOutput _ 'Output = ()
  IsOutput _ 'InputOutput = ()
  IsOutput fact dir = TypeError
    ( 'Text "You tried to use an " ':<>: 'ShowType (FormatDirection dir) ':<>: 'Text " fact of type " ':<>: 'ShowType fact ':<>: 'Text " as an output."
    ':$$: 'Text "Possible solution: change the FactDirection of " ':<>: 'ShowType fact
      ':<>: 'Text " to either 'Output' or 'InputOutput'."
    )

type FormatDirection :: Direction -> Symbol
type family FormatDirection dir where
  FormatDirection 'Output = "output"
  FormatDirection 'Input = "input"
  FormatDirection 'Internal = "internal"

-- | A helper type family for checking if a specific Souffle `Program` contains
--   a certain `Fact`. This constraint will generate a user-friendly type error
--   if this is not the case.
type ContainsFact :: Type -> Type -> Constraint
type family ContainsFact prog fact where
  ContainsFact prog fact =
    CheckContains prog (ProgramFacts prog) fact

type CheckContains :: Type -> [Type] -> Type -> Constraint
type family CheckContains prog facts fact :: Constraint where
  CheckContains prog '[] fact =
    TypeError ('Text "You tried to perform an action with a fact of type '" ':<>: 'ShowType fact
    ':<>: 'Text "' for program '" ':<>: 'ShowType prog ':<>: 'Text "'."
    ':$$: 'Text "The program contains the following facts: " ':<>: 'ShowType (ProgramFacts prog) ':<>: 'Text "."
    ':$$: 'Text "It does not contain fact: " ':<>: 'ShowType fact ':<>: 'Text "."
    ':$$: 'Text "You can fix this error by adding the type '" ':<>: 'ShowType fact
    ':<>: 'Text "' to the ProgramFacts type in the Program instance for " ':<>: 'ShowType prog ':<>: 'Text ".")
  CheckContains _ (a ': _) a = ()
  CheckContains prog (_ ': as) b = CheckContains prog as b

-- | A typeclass for describing a datalog program.
--
-- Example usage (assuming the program was generated from path.dl
-- and contains 2 facts: Edge and Reachable):
--
-- @
-- data Path = Path  -- Handle for the datalog program
--
-- instance Program Path where
--   type ProgramFacts Path = '[Edge, Reachable]
--   programName = const "path"
-- @
type Program :: Type -> Constraint
class Program a where
  -- | A type level list of facts that belong to this program.
  --   This list is used to check that only known facts are added to a program.
  type ProgramFacts a :: [Type]

  -- | Function for obtaining the name of a Datalog program.
  --   This has to be the same as the name of the .dl file (minus the extension).
  programName :: a -> String

-- | A helper data type, used in combination with the DerivingVia extension to
--   automatically generate code to bind Haskell to a Souffle Datalog program.
--
-- The following is an example how to bind to a Datalog program "path"
-- (saved as path.dl / path.cpp), that uses two facts called "edge" and
-- "reachable" (represented with the Edge and Reachable types):
--
-- @
-- data Path = Path
--   deriving Souffle.Program
--   via Souffle.ProgramOptions Path "path" '[Edge, Reachable]
-- @
--
-- See also: 'FactOptions'.
type ProgramOptions :: Type -> Symbol -> [Type] -> Type
newtype ProgramOptions prog progName facts = ProgramOptions prog
type role ProgramOptions representational phantom phantom

instance KnownSymbol progName => Program (ProgramOptions prog progName facts) where
  type ProgramFacts (ProgramOptions _ _ facts) = facts

  programName :: KnownSymbol progName => ProgramOptions prog progName facts -> String
  programName = const $ symbolVal (Proxy @progName)
  {-# INLINABLE programName #-}

-- | A typeclass for data types representing a fact in datalog.
--
-- Example usage:
--
-- @
-- instance Fact Edge where
--   type FactDirection Edge = 'Input
--   factName = const "edge"
-- @
type Fact :: Type -> Constraint
class Marshal.Marshal a => Fact a where
  -- | The direction or "mode" a fact can be used in.
  --   This is used to perform compile-time checks that a fact is only used
  --   in valid situations. For more information, see the 'Direction' type.
  type FactDirection a :: Direction

  -- | Function for obtaining the name of a fact
  --   (has to be the same as described in the Datalog program).
  --
  -- It uses a 'Proxy' to select the correct instance.
  factName :: Proxy a -> String

-- | A helper data type, used in combination with the DerivingVia extension to
--   automatically generate code to bind a Haskell datatype to a Souffle
--   Datalog fact.
--
-- The following is an example how to bind to a Datalog fact "edge"
-- that contains two symbols (strings in Haskell) that is an input (from the
-- Datalog point of view):
--
-- @
-- data Edge = Edge String String
--   deriving (Eq, Show, Generic)
--   deriving anyclass Souffle.Marshal
--   deriving Souffle.Fact
--   via Souffle.FactOptions Edge "edge" 'Souffle.Input
-- @
--
-- See also: 'ProgramOptions'.
type FactOptions :: Type -> Symbol -> Direction -> Type
newtype FactOptions fact factName dir = FactOptions fact
type role FactOptions representational phantom phantom

instance Marshal.Marshal fact => Marshal.Marshal (FactOptions fact name dir) where
  push :: (Marshal.Marshal fact, Marshal.MonadPush m) => FactOptions fact name dir -> m ()
  push (FactOptions fact) = Marshal.push fact
  {-# INLINABLE push #-}

  pop :: (Marshal.Marshal fact, Marshal.MonadPop m) => m (FactOptions fact name dir)
  pop = FactOptions <$> Marshal.pop
  {-# INLINABLE pop #-}

instance ( Marshal.Marshal fact
         , KnownSymbol name
         ) => Fact (FactOptions fact name dir) where
  type FactDirection (FactOptions _ _ dir) = dir

  factName :: (Marshal.Marshal fact, KnownSymbol name) => Proxy (FactOptions fact name dir) -> String
  factName = const $ symbolVal (Proxy @name)
  {-# INLINABLE factName #-}


-- | A datatype describing which operations a certain fact supports.
--   The direction is from the datalog perspective, so that it
--   aligns with ".decl" statements in Souffle.
type Direction :: Type
data Direction
  = Input
  -- ^ Fact can only be stored in Datalog (using `addFact`/`addFacts`).
  | Output
  -- ^ Fact can only be read from Datalog (using `getFacts`/`findFact`).
  | InputOutput
  -- ^ Fact supports both reading from / writing to Datalog.
  | Internal
  -- ^ Supports neither reading from / writing to Datalog. This is used for
  --   facts that are only visible inside Datalog itself.

-- | A mtl-style typeclass for Souffle-related actions.
type MonadSouffle :: (Type -> Type) -> Constraint
class Monad m => MonadSouffle m where
  -- | Represents a handle for interacting with a Souffle program.
  --
  --   The handle is used in all other functions of this typeclass to perform
  --   Souffle-related actions.
  type Handler m :: Type -> Type

  -- | Helper associated type constraint that allows collecting facts from
  --   Souffle in a list or vector. Only used internally.
  type CollectFacts m (c :: Type -> Type) :: Constraint
  -- | Helper associated type constraint that allows submitting facts to
  --   Souffle. Only used internally.
  type SubmitFacts m (a :: Type) :: Constraint

  -- | Runs the Souffle program.
  run :: Handler m prog -> m ()

  -- | Sets the number of CPU cores this Souffle program should use.
  setNumThreads :: Handler m prog -> Word64 -> m ()

  -- | Gets the number of CPU cores this Souffle program should use.
  getNumThreads :: Handler m prog -> m Word64

  -- | Returns all facts of a program. This function makes use of type inference
  --   to select the type of fact to return.
  getFacts :: (Fact a, ContainsOutputFact prog a, CollectFacts m c)
           => Handler m prog -> m (c a)

  -- | Searches for a fact in a program.
  --   Returns 'Nothing' if no matching fact was found; otherwise 'Just' the fact.
  --
  --   Conceptually equivalent to @List.find (== fact) \<$\> getFacts prog@,
  --   but this operation can be implemented much faster.
  findFact :: (Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts m a)
           => Handler m prog -> a -> m (Maybe a)

  -- | Adds a fact to the program.
  addFact :: (Fact a, ContainsInputFact prog a, SubmitFacts m a, Show a)
          => Handler m prog -> a -> m ()

  -- | Adds multiple facts to the program. This function could be implemented
  --   in terms of 'addFact', but this is done as a minor optimization.
  addFacts :: (Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts m a)
           => Handler m prog -> t a -> m ()

instance MonadSouffle m => MonadSouffle (ReaderT r m) where
  type Handler      (ReaderT r m)   = Handler m
  type CollectFacts (ReaderT r m) c = CollectFacts m c
  type SubmitFacts  (ReaderT r m) a = SubmitFacts m a

  run :: MonadSouffle m => Handler (ReaderT r m) prog -> ReaderT r m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: MonadSouffle m => Handler (ReaderT r m) prog -> Word64 -> ReaderT r m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: MonadSouffle m => Handler (ReaderT r m) prog -> ReaderT r m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, CollectFacts (ReaderT r m) c)
           => Handler (ReaderT r m) prog -> ReaderT r m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (ReaderT r m) a)
           => Handler (ReaderT r m) prog -> a -> ReaderT r m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Fact a, ContainsInputFact prog a, SubmitFacts (ReaderT r m) a, Show a)
          => Handler (ReaderT r m) prog -> a -> ReaderT r m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (ReaderT r m) a)
           => Handler (ReaderT r m) prog -> t a -> ReaderT r m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance (Monoid w, MonadSouffle m) => MonadSouffle (WriterT w m) where
  type Handler      (WriterT w m)   = Handler m
  type CollectFacts (WriterT w m) c = CollectFacts m c
  type SubmitFacts  (WriterT w m) a = SubmitFacts m a

  run :: (Monoid w, MonadSouffle m) => Handler (WriterT w m) prog -> WriterT w m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: (Monoid w, MonadSouffle m) => Handler (WriterT w m) prog -> Word64 -> WriterT w m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: (Monoid w, MonadSouffle m) => Handler (WriterT w m) prog -> WriterT w m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (Monoid w, MonadSouffle m, Fact a, ContainsOutputFact prog a, CollectFacts (WriterT w m) c)
           => Handler (WriterT w m) prog -> WriterT w m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (Monoid w, MonadSouffle m, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (WriterT w m) a)
           => Handler (WriterT w m) prog -> a -> WriterT w m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (Monoid w, MonadSouffle m, Fact a, ContainsInputFact prog a, SubmitFacts (WriterT w m) a, Show a)
          => Handler (WriterT w m) prog -> a -> WriterT w m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (Monoid w, MonadSouffle m, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (WriterT w m) a)
           => Handler (WriterT w m) prog -> t a -> WriterT w m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance MonadSouffle m => MonadSouffle (LazyState.StateT s m) where
  type Handler      (LazyState.StateT s m)   = Handler m
  type CollectFacts (LazyState.StateT s m) c = CollectFacts m c
  type SubmitFacts  (LazyState.StateT s m) a = SubmitFacts m a

  run :: MonadSouffle m => Handler (LazyState.StateT s m) prog -> LazyState.StateT s m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: MonadSouffle m =>
    Handler (LazyState.StateT s m) prog -> Word64 -> LazyState.StateT s m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: MonadSouffle m =>
    Handler (LazyState.StateT s m) prog -> LazyState.StateT s m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, CollectFacts (LazyState.StateT s m) c) =>
    Handler (LazyState.StateT s m) prog -> LazyState.StateT s m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (LazyState.StateT s m) a) =>
    Handler (LazyState.StateT s m) prog -> a -> LazyState.StateT s m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Fact a, ContainsInputFact prog a, SubmitFacts (LazyState.StateT s m) a, Show a) =>
    Handler (LazyState.StateT s m) prog -> a -> LazyState.StateT s m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (LazyState.StateT s m) a) =>
    Handler (LazyState.StateT s m) prog -> t a -> LazyState.StateT s m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance MonadSouffle m => MonadSouffle (StrictState.StateT s m) where
  type Handler      (StrictState.StateT s m)   = Handler m
  type CollectFacts (StrictState.StateT s m) c = CollectFacts m c
  type SubmitFacts  (StrictState.StateT s m) a = SubmitFacts m a

  run :: MonadSouffle m => Handler (StrictState.StateT s m) prog -> StrictState.StateT s m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: MonadSouffle m =>
    Handler (StrictState.StateT s m) prog -> Word64 -> StrictState.StateT s m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: MonadSouffle m =>
    Handler (StrictState.StateT s m) prog -> StrictState.StateT s m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, CollectFacts (StrictState.StateT s m) c) =>
    Handler (StrictState.StateT s m) prog -> StrictState.StateT s m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (StrictState.StateT s m) a) =>
    Handler (StrictState.StateT s m) prog -> a -> StrictState.StateT s m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Fact a, ContainsInputFact prog a, SubmitFacts (StrictState.StateT s m) a, Show a) =>
    Handler (StrictState.StateT s m) prog -> a -> StrictState.StateT s m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (StrictState.StateT s m) a) =>
    Handler (StrictState.StateT s m) prog -> t a -> StrictState.StateT s m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance (MonadSouffle m, Monoid w) => MonadSouffle (LazyRWS.RWST r w s m) where
  type Handler      (LazyRWS.RWST r w s m)   = Handler m
  type CollectFacts (LazyRWS.RWST r w s m) c = CollectFacts m c
  type SubmitFacts  (LazyRWS.RWST r w s m) a = SubmitFacts m a

  run :: (MonadSouffle m, Monoid w) =>
    Handler (LazyRWS.RWST r w s m) prog -> LazyRWS.RWST r w s m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: (MonadSouffle m, Monoid w) =>
    Handler (LazyRWS.RWST r w s m) prog -> Word64 -> LazyRWS.RWST r w s m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: (MonadSouffle m, Monoid w) =>
    Handler (LazyRWS.RWST r w s m) prog -> LazyRWS.RWST r w s m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Monoid w, Fact a, ContainsOutputFact prog a, CollectFacts (LazyRWS.RWST r w s m) c) =>
    Handler (LazyRWS.RWST r w s m) prog -> LazyRWS.RWST r w s m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Monoid w, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (LazyRWS.RWST r w s m) a) =>
   Handler (LazyRWS.RWST r w s m) prog -> a -> LazyRWS.RWST r w s m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Monoid w, Fact a, ContainsInputFact prog a, SubmitFacts (LazyRWS.RWST r w s m) a, Show a) =>
    Handler (LazyRWS.RWST r w s m) prog -> a -> LazyRWS.RWST r w s m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Monoid w, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (LazyRWS.RWST r w s m) a) =>
    Handler (LazyRWS.RWST r w s m) prog -> t a -> LazyRWS.RWST r w s m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance (MonadSouffle m, Monoid w) => MonadSouffle (StrictRWS.RWST r w s m) where
  type Handler      (StrictRWS.RWST r w s m)   = Handler m
  type CollectFacts (StrictRWS.RWST r w s m) c = CollectFacts m c
  type SubmitFacts  (StrictRWS.RWST r w s m) a = SubmitFacts m a

  run :: (MonadSouffle m, Monoid w) => Handler (StrictRWS.RWST r w s m) prog -> StrictRWS.RWST r w s m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: (MonadSouffle m, Monoid w) =>
    Handler (StrictRWS.RWST r w s m) prog -> Word64 -> StrictRWS.RWST r w s m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: (MonadSouffle m, Monoid w) =>
    Handler (StrictRWS.RWST r w s m) prog -> StrictRWS.RWST r w s m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Monoid w, Fact a, ContainsOutputFact prog a, CollectFacts (StrictRWS.RWST r w s m) c) =>
    Handler (StrictRWS.RWST r w s m) prog -> StrictRWS.RWST r w s m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Monoid w, Fact a, ContainsOutputFact prog a, Eq a, SubmitFacts (StrictRWS.RWST r w s m) a) =>
    Handler (StrictRWS.RWST r w s m) prog -> a -> StrictRWS.RWST r w s m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Monoid w, Fact a, ContainsInputFact prog a, SubmitFacts (StrictRWS.RWST r w s m) a, Show a) =>
    Handler (StrictRWS.RWST r w s m) prog -> a -> StrictRWS.RWST r w s m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Monoid w, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (StrictRWS.RWST r w s m) a) =>
    Handler (StrictRWS.RWST r w s m) prog -> t a -> StrictRWS.RWST r w s m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

instance MonadSouffle m => MonadSouffle (ExceptT e m) where
  type Handler      (ExceptT e m)   = Handler m
  type CollectFacts (ExceptT e m) c = CollectFacts m c
  type SubmitFacts  (ExceptT e m) a = SubmitFacts m a

  run :: MonadSouffle m => Handler (ExceptT e m) prog -> ExceptT e m ()
  run = lift . run
  {-# INLINABLE run #-}

  setNumThreads :: MonadSouffle m =>
    Handler (ExceptT e m) prog -> Word64 -> ExceptT e m ()
  setNumThreads prog = lift . setNumThreads prog
  {-# INLINABLE setNumThreads #-}

  getNumThreads :: MonadSouffle m => Handler (ExceptT e m) prog -> ExceptT e m Word64
  getNumThreads = lift . getNumThreads
  {-# INLINABLE getNumThreads #-}

  getFacts :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, CollectFacts (ExceptT e m) c) =>
    Handler (ExceptT e m) prog -> ExceptT e m (c a)
  getFacts = lift . getFacts
  {-# INLINABLE getFacts #-}

  findFact :: (MonadSouffle m, Fact a, ContainsOutputFact prog a, Eq a,SubmitFacts (ExceptT e m) a) =>
    Handler (ExceptT e m) prog -> a -> ExceptT e m (Maybe a)
  findFact prog = lift . findFact prog
  {-# INLINABLE findFact #-}

  addFact :: (MonadSouffle m, Fact a, ContainsInputFact prog a, SubmitFacts (ExceptT e m) a, Show a) =>
    Handler (ExceptT e m) prog -> a -> ExceptT e m ()
  addFact fact = lift . addFact fact
  {-# INLINABLE addFact #-}

  addFacts :: (MonadSouffle m, Foldable t, Fact a, ContainsInputFact prog a, SubmitFacts (ExceptT e m) a) =>
    Handler (ExceptT e m) prog -> t a -> ExceptT e m ()
  addFacts facts = lift . addFacts facts
  {-# INLINABLE addFacts #-}

-- | A mtl-style typeclass for Souffle-related actions that involve file IO.
type MonadSouffleFileIO :: (Type -> Type) -> Constraint
class MonadSouffle m => MonadSouffleFileIO m where
  -- | Load all facts from files in a certain directory.
  loadFiles :: Handler m prog -> FilePath -> m ()

  -- | Write out all facts of the program to CSV files in a certain directory
  --   (as defined in the Souffle program).
  writeFiles :: Handler m prog -> FilePath -> m ()

instance MonadSouffleFileIO m => MonadSouffleFileIO (ReaderT r m) where
  loadFiles :: MonadSouffleFileIO m =>
    Handler (ReaderT r m) prog -> FilePath -> ReaderT r m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: MonadSouffleFileIO m =>
    Handler (ReaderT r m) prog -> FilePath -> ReaderT r m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance (Monoid w, MonadSouffleFileIO m) => MonadSouffleFileIO (WriterT w m) where
  loadFiles :: (Monoid w, MonadSouffleFileIO m) =>
    Handler (WriterT w m) prog -> FilePath -> WriterT w m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: (Monoid w, MonadSouffleFileIO m) =>
    Handler (WriterT w m) prog -> FilePath -> WriterT w m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance MonadSouffleFileIO m => MonadSouffleFileIO (StrictState.StateT s m) where
  loadFiles :: MonadSouffleFileIO m =>
    Handler (StrictState.StateT s m) prog -> FilePath -> StrictState.StateT s m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: MonadSouffleFileIO m =>
    Handler (StrictState.StateT s m) prog -> FilePath -> StrictState.StateT s m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance MonadSouffleFileIO m => MonadSouffleFileIO (LazyState.StateT s m) where
  loadFiles :: MonadSouffleFileIO m =>
    Handler (LazyState.StateT s m) prog -> FilePath -> LazyState.StateT s m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: MonadSouffleFileIO m =>
    Handler (LazyState.StateT s m) prog -> FilePath -> LazyState.StateT s m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance (MonadSouffleFileIO m, Monoid w) => MonadSouffleFileIO (LazyRWS.RWST r w s m) where
  loadFiles :: (MonadSouffleFileIO m, Monoid w) =>
    Handler (LazyRWS.RWST r w s m) prog -> FilePath -> LazyRWS.RWST r w s m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: (MonadSouffleFileIO m, Monoid w)
             => Handler (LazyRWS.RWST r w s m) prog -> FilePath -> LazyRWS.RWST r w s m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance (MonadSouffleFileIO m, Monoid w) => MonadSouffleFileIO (StrictRWS.RWST r w s m) where
  loadFiles :: (MonadSouffleFileIO m, Monoid w) =>
    Handler (StrictRWS.RWST r w s m) prog -> FilePath -> StrictRWS.RWST r w s m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: (MonadSouffleFileIO m, Monoid w) =>
    Handler (StrictRWS.RWST r w s m) prog -> FilePath -> StrictRWS.RWST r w s m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

instance MonadSouffleFileIO m => MonadSouffleFileIO (ExceptT s m) where
  loadFiles :: MonadSouffleFileIO m => Handler (ExceptT s m) prog -> FilePath -> ExceptT s m ()
  loadFiles prog = lift . loadFiles prog
  {-# INLINABLE loadFiles #-}

  writeFiles :: MonadSouffleFileIO m => Handler (ExceptT s m) prog -> FilePath -> ExceptT s m ()
  writeFiles prog = lift . writeFiles prog
  {-# INLINABLE writeFiles #-}

