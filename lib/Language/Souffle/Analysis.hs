-- | This module provides an 'Analysis' type for combining multiple Datalog
--   analyses together. Composition of analyses is done via the various
--   type-classes that are implemented for this type. For a longer explanation
--   of how the 'Analysis' type works, see this
--   <https://luctielen.com/posts/analyses_are_arrows/ blogpost>.
--
--   If you are just starting out using this library, you are probably better
--   of taking a look at the "Language.Souffle.Interpreted" module instead to
--   start interacting with a single Datalog program.
module Language.Souffle.Analysis
  ( Analysis
  , mkAnalysis
  , execAnalysis
  ) where

import           Control.Arrow    (Arrow (..), ArrowChoice (..))
import           Control.Category (Category (..))
import           Control.Monad    ((>=>))

import           Data.Kind        (Type)
import           Data.Profunctor  (Choice (..), Profunctor (..), Strong (..))

import           Prelude          hiding (id, (.))

-- | Data type used to compose multiple Datalog programs. Composition is mainly
--   done via the various type-classes implemented for this type.
--   Values of this type can be created using 'mkAnalysis'.
--
--   The @m@ type-variable represents the monad the analysis will run in. In
--   most cases, this will be the @SouffleM@ monad from either
--   "Language.Souffle.Compiled" or "Language.Souffle.Interpreted".
--   The @a@ and @b@ type-variables represent respectively the input and output
--   types of the analysis.
type Analysis :: (Type -> Type) -> Type -> Type -> Type
data Analysis m a b
  = Analysis (a -> m ()) (m ()) (a -> m b)
type role Analysis representational representational nominal

-- | Creates an 'Analysis' value.
mkAnalysis :: (a -> m ()) -- ^ Function for finding facts used by the 'Analysis'.
           -> m ()        -- ^ Function for actually running the 'Analysis'.
           -> m b         -- ^ Function for retrieving the 'Analysis' results from Souffle.
           -> Analysis m a b
mkAnalysis f r g = Analysis f r (const g)
{-# INLINABLE mkAnalysis #-}

-- | Converts an 'Analysis' into an effectful function, so it can be executed.
execAnalysis :: Applicative m => Analysis m a b -> (a -> m b)
execAnalysis (Analysis f r g) a = f a *> r *> g a
{-# INLINABLE execAnalysis #-}

instance Functor m => Functor (Analysis m a) where
  fmap :: Functor m => (a1 -> b) -> Analysis m a a1 -> Analysis m a b
  fmap func (Analysis f r g) =
    Analysis f r (fmap func <$> g)
  {-# INLINABLE fmap #-}

instance Functor m => Profunctor (Analysis m) where
  lmap :: Functor m => (a -> b) -> Analysis m b c -> Analysis m a c
  lmap fn (Analysis f r g) =
    Analysis (lmap fn f) r (lmap fn g)
  {-# INLINABLE lmap #-}

  rmap :: Functor m => (b -> c) -> Analysis m a b -> Analysis m a c
  rmap = fmap
  {-# INLINABLE rmap #-}

instance (Monoid (m ()), Applicative m) => Applicative (Analysis m a) where
  pure :: (Monoid (m ()), Applicative m) => a1 -> Analysis m a a1
  pure a = Analysis mempty mempty (const $ pure a)
  {-# INLINABLE pure #-}

  (<*>) :: (Monoid (m ()), Applicative m) => Analysis m a (a1 -> b) -> Analysis m a a1 -> Analysis m a b
  Analysis f1 r1 g1 <*> Analysis f2 r2 g2 =
    Analysis (f1 <> f2) (r1 <> r2) (\a -> g1 a <*> g2 a)
  {-# INLINABLE (<*>) #-}

instance (Semigroup (m ()), Semigroup (m b)) => Semigroup (Analysis m a b) where
  (<>) :: (Semigroup (m ()), Semigroup (m b)) => Analysis m a b -> Analysis m a b -> Analysis m a b
  Analysis f1 r1 g1 <> Analysis f2 r2 g2 =
    Analysis (f1 <> f2) (r1 <> r2) (g1 <> g2)
  {-# INLINABLE (<>) #-}

instance (Monoid (m ()), Monoid (m b)) => Monoid (Analysis m a b) where
  mempty :: (Monoid (m ()), Monoid (m b)) => Analysis m a b
  mempty = Analysis mempty mempty mempty
  {-# INLINABLE mempty #-}

instance (Monoid (m ()), Monad m) => Category (Analysis m) where
  id :: (Monoid (m ()), Monad m) => Analysis m a a
  id = Analysis mempty mempty pure
  {-# INLINABLE id #-}

  Analysis f1 r1 g1 . Analysis f2 r2 g2 = Analysis f r1 g
    where
      f = execAnalysis (Analysis f2 r2 g2) >=> f1
      -- NOTE: lazyness avoids work here in g2 in cases where "const" is used
      g = g2 >=> g1
  {-# INLINABLE (.) #-}

instance Functor m => Strong (Analysis m) where
  first' :: Functor m => Analysis m a b -> Analysis m (a, c) (b, c)
  first' (Analysis f r g) =
    Analysis (f . fst) r $ \(b, d) -> (,d) <$> g b
  {-# INLINABLE first' #-}

  second' :: Functor m => Analysis m a b -> Analysis m (c, a) (c, b)
  second' (Analysis f r g) =
    Analysis (f . snd) r $ \(d, b) -> (d,) <$> g b
  {-# INLINABLE second' #-}

instance Applicative m => Choice (Analysis m) where
  left' :: Applicative m => Analysis m a b -> Analysis m (Either a c) (Either b c)
  left' (Analysis f r g) = Analysis f' r g'
    where
      f' = \case
        Left b -> f b
        Right _ -> pure ()
      g' = \case
        Left b -> Left <$> g b
        Right d -> pure $ Right d
  {-# INLINABLE left' #-}

  right' :: Applicative m => Analysis m a b -> Analysis m (Either c a) (Either c b)
  right' (Analysis f r g) = Analysis f' r g'
    where
      f' = \case
        Left _ -> pure ()
        Right b -> f b
      g' = \case
        Left d -> pure $ Left d
        Right b -> Right <$> g b
  {-# INLINABLE right' #-}

instance (Monad m, Monoid (m ()), Category (Analysis m)) => Arrow (Analysis m) where
  arr :: (Monad m, Monoid (m ()), Category (Analysis m)) => (b -> c) -> Analysis m b c
  arr f = Analysis mempty mempty (pure . f)
  {-# INLINABLE arr #-}

  first :: (Monad m, Monoid (m ()), Category (Analysis m)) => Analysis m b c -> Analysis m (b, d) (c, d)
  first = first'
  {-# INLINABLE first #-}

  second :: (Monad m, Monoid (m ()), Category (Analysis m)) => Analysis m b c -> Analysis m (d, b) (d, c)
  second = second'
  {-# INLINABLE second #-}

  (***) :: (Monad m, Monoid (m ()), Category (Analysis m)) => Analysis m b c -> Analysis m b' c' -> Analysis m (b, b') (c, c')
  Analysis f1 r1 g1 *** Analysis f2 r2 g2 =
    Analysis (\(b, b') -> f1 b *> f2 b') (r1 <> r2) $ \(b, b') -> do
      c <- g1 b
      c' <- g2 b'
      pure (c, c')
  {-# INLINABLE (***) #-}

  (&&&) :: (Monad m, Monoid (m ()), Category (Analysis m)) => Analysis m b c -> Analysis m b c' -> Analysis m b (c, c')
  Analysis f1 r1 g1 &&& Analysis f2 r2 g2 =
    Analysis (f1 <> f2) (r1 <> r2) $ \b -> (,) <$> g1 b <*> g2 b
  {-# INLINABLE (&&&) #-}

instance (Monad m, Monoid (m ())) => ArrowChoice (Analysis m) where
  left :: (Monad m, Monoid (m ())) => Analysis m b c -> Analysis m (Either b d) (Either c d)
  left = left'
  {-# INLINABLE left #-}

  right :: (Monad m, Monoid (m ())) => Analysis m b c -> Analysis m (Either d b) (Either d c)
  right = right'
  {-# INLINABLE right #-}

  (+++) :: (Monad m, Monoid (m ())) => Analysis m b c -> Analysis m b' c' -> Analysis m (Either b b') (Either c c')
  Analysis f1 r1 g1 +++ Analysis f2 r2 g2 = Analysis f' (r1 <> r2) g'
    where
      f' = \case
        Left b -> f1 b
        Right b' -> f2 b'
      g' = \case
        Left b -> Left <$> g1 b
        Right b' -> Right <$> g2 b'
  {-# INLINABLE (+++) #-}

