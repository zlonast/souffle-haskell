
{-# LANGUAGE DeriveGeneric, TypeFamilies, DataKinds #-}

module Test.Language.Souffle.MarshalSpec
  ( module Test.Language.Souffle.MarshalSpec
  ) where

import Test.Hspec
import Test.Hspec.Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import GHC.Generics
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Text
import Data.Int
import Data.Word
import Data.Maybe ( fromJust )
import Control.Monad.IO.Class ( liftIO )
import Language.Souffle.Marshal
import qualified Language.Souffle.Interpreted as Souffle


data Edge = Edge String String
  deriving (Eq, Show, Generic)

newtype EdgeUInt = EdgeUInt Word32
  deriving (Eq, Show, Generic)

newtype FloatValue = FloatValue Float
  deriving (Eq, Show, Generic)

data EdgeStrict = EdgeStrict !String !String
  deriving (Eq, Show, Generic)

data EdgeUnpacked
  = EdgeUnpacked {-# UNPACK #-} !Int32 {-# UNPACK #-} !Int32
  deriving (Eq, Show, Generic)

type Vertex = Text
type Vertex' = Text

data EdgeSynonyms = EdgeSynonyms Vertex Vertex
  deriving (Eq, Show, Generic)

data EdgeMultipleSynonyms = EdgeMultipleSynonyms Vertex Vertex'
  deriving (Eq, Show, Generic)

data EdgeMixed = EdgeMixed Text Vertex
  deriving (Eq, Show, Generic)

data EdgeRecord
  = EdgeRecord
  { fromNode :: Text
  , toNode :: Text
  } deriving (Eq, Show, Generic)

data IntsAndStrings = IntsAndStrings Text Int32 Text
  deriving (Eq, Show, Generic)

data LargeRecord
  = LargeRecord Int32 Int32 Int32 Int32
  deriving (Eq, Show, Generic)


instance Marshal Edge
instance Marshal EdgeUInt
instance Marshal FloatValue
instance Marshal EdgeStrict
instance Marshal EdgeUnpacked
instance Marshal EdgeSynonyms
instance Marshal EdgeMultipleSynonyms
instance Marshal EdgeMixed
instance Marshal EdgeRecord
instance Marshal IntsAndStrings
instance Marshal LargeRecord


data RoundTrip = RoundTrip

newtype StringFact = StringFact String
  deriving (Eq, Show, Generic)

newtype TextFact = TextFact T.Text
  deriving (Eq, Show, Generic)

newtype LazyTextFact = LazyTextFact TL.Text
  deriving (Eq, Show, Generic)

newtype Int32Fact = Int32Fact Int32
  deriving (Eq, Show, Generic)

newtype Word32Fact = Word32Fact Word32
  deriving (Eq, Show, Generic)

newtype FloatFact = FloatFact Float
  deriving (Eq, Show, Generic)

instance Souffle.Fact StringFact where
  factName = const "string_fact"

instance Souffle.Fact TextFact where
  factName = const "string_fact"

instance Souffle.Fact LazyTextFact where
  factName = const "string_fact"

instance Souffle.Fact Int32Fact where
  factName = const "number_fact"

instance Souffle.Fact Word32Fact where
  factName = const "unsigned_fact"

instance Souffle.Fact FloatFact where
  factName = const "float_fact"

instance Souffle.Marshal StringFact
instance Souffle.Marshal TextFact
instance Souffle.Marshal LazyTextFact
instance Souffle.Marshal Int32Fact
instance Souffle.Marshal Word32Fact
instance Souffle.Marshal FloatFact

instance Souffle.Program RoundTrip where
  type ProgramFacts RoundTrip = 
    [StringFact, TextFact, LazyTextFact, Int32Fact, Word32Fact, FloatFact]
  programName = const "round_trip"


spec :: Spec
spec = describe "Marshalling" $ parallel $ do
  describe "Auto-deriving marshalling code" $
    it "can generate code for all instances in this file" $
      -- If this file compiles, then the test has already passed
      42 `shouldBe` 42

  describe "data transfer between Haskell and Souffle" $ parallel $ do
    let run fact = liftIO $ Souffle.runSouffle $ do
          handle <- fromJust <$> Souffle.init RoundTrip
          Souffle.addFact handle fact
          Souffle.run handle
          fact' <- Prelude.head <$> Souffle.getFacts handle
          Souffle.cleanup handle
          pure fact'

    it "can serialize and deserialize String values" $ hedgehog $ do
      str <- forAll $ Gen.string (Range.linear 0 10) Gen.unicode
      let fact = StringFact str
      fact' <- run fact
      fact === fact'

    it "can serialize and deserialize lazy Text" $ hedgehog $ do
      str <- forAll $ Gen.string (Range.linear 0 10) Gen.unicode
      let fact = LazyTextFact (TL.pack str)
      fact' <- run fact
      fact === fact'

    it "can serialize and deserialize strict Text values" $ hedgehog $ do
      str <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode
      let fact = TextFact str
      fact' <- run fact
      fact === fact'

    it "can serialize and deserialize Int32 values" $ hedgehog $ do
      x <- forAll $ Gen.int32 (Range.linear minBound maxBound)
      let fact = Int32Fact x
      fact' <- run fact
      fact === fact'

    it "can serialize and deserialize Word32 values" $ hedgehog $ do
      x <- forAll $ Gen.word32 (Range.linear minBound maxBound)
      let fact = Word32Fact x
      fact' <- run fact
      fact === fact'

    {- TODO: enable this test once souffle floating point conversions are fixed
    it "can serialize and deserialize Float values" $ hedgehog $ do
      let epsilon = 1e-6
          fmin = -1e9
          fmax =  1e9
      x <- forAll $ Gen.float (Range.exponentialFloat fmin fmax)
      let fact = FloatFact x
      FloatFact x' <- run fact
      (abs (x' - x) < epsilon) === True
    -}