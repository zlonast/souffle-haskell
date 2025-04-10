{-# OPTIONS_GHC -Wno-x-partial -Wno-unrecognised-warning-flags #-}
{-# LANGUAGE NoPolyKinds #-}
module Test.Language.Souffle.MarshalSpec
  ( module Test.Language.Souffle.MarshalSpec
  ) where

import           Control.Monad                (join)
import           Control.Monad.IO.Class       (liftIO)

import           Data.Int                     (Int32)
import           Data.List                    (List)
import           Data.Maybe                   (fromJust)
import           Data.Proxy                   (Proxy)
import           Data.String                  (IsString)
import           Data.Text                    (Text)
import qualified Data.Text                    as T
import qualified Data.Text.Lazy               as TL
import           Data.Void                    (Void)
import           Data.Word                    (Word32)

import           GHC.Generics                 (Generic)
import           GHC.Tuple                    (Tuple3)

import qualified Hedgehog.Gen                 as Gen
import qualified Hedgehog.Range               as Range

import qualified Language.Souffle.Class       as Souffle
import qualified Language.Souffle.Compiled    as Compiled
import qualified Language.Souffle.Interpreted as Interpreted
import           Language.Souffle.Marshal     (Marshal)

import           Test.Hspec                   (Spec, describe, it, parallel, shouldBe)
import           Test.Hspec.Hedgehog          (PropertyT, forAll, hedgehog, (===))



data Edge = Edge String String
  deriving stock (Eq, Show, Generic)

newtype EdgeUInt = EdgeUInt Word32
  deriving stock (Eq, Show, Generic)

newtype FloatValue = FloatValue Float
  deriving stock (Eq, Show, Generic)

data EdgeStrict = EdgeStrict !String !String
  deriving stock (Eq, Show, Generic)

data EdgeUnpacked
  = EdgeUnpacked {-# UNPACK #-} !Int32 {-# UNPACK #-} !Int32
  deriving stock (Eq, Show, Generic)

type Vertex = Text
type Vertex' = Text

data EdgeSynonyms = EdgeSynonyms Vertex Vertex
  deriving stock (Eq, Show, Generic)

data EdgeMultipleSynonyms = EdgeMultipleSynonyms Vertex Vertex'
  deriving stock (Eq, Show, Generic)

data EdgeMixed = EdgeMixed Text Vertex
  deriving stock (Eq, Show, Generic)

data EdgeRecord
  = EdgeRecord
  { fromNode :: Text
  , toNode   :: Text
  } deriving stock (Eq, Show, Generic)

data IntsAndStrings = IntsAndStrings Text Int32 Text
  deriving stock (Eq, Show, Generic)

data LargeRecord
  = LargeRecord Int32 Int32 Int32 Int32
  deriving stock (Eq, Show, Generic)

newtype NestedNewtype = NestedNewtype LargeRecord
  deriving stock (Eq, Show, Generic)

data Pair = Pair Int32 Int32
  deriving stock (Eq, Show, Generic)

data NestedRecord = NestedRecord Pair Pair
  deriving stock (Eq, Show, Generic)

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
instance Marshal Pair
instance Marshal NestedNewtype
instance Marshal NestedRecord

data RoundTrip = RoundTrip

newtype StringFact = StringFact String
  deriving stock (Eq, Show, Generic)

newtype TextFact = TextFact T.Text
  deriving stock (Eq, Show, Generic)

newtype LazyTextFact = LazyTextFact TL.Text
  deriving stock (Eq, Show, Generic)

newtype Int32Fact = Int32Fact Int32
  deriving stock (Eq, Show, Generic)

newtype Word32Fact = Word32Fact Word32
  deriving stock (Eq, Show, Generic)

newtype FloatFact = FloatFact Float
  deriving stock (Eq, Show, Generic)

instance Souffle.Fact StringFact where
  type FactDirection StringFact = Souffle.InputOutput

  factName :: Proxy StringFact -> String
  factName = const "string_fact"

instance Souffle.Fact TextFact where
  type FactDirection TextFact = Souffle.InputOutput

  factName :: Proxy TextFact -> String
  factName = const "string_fact"

instance Souffle.Fact LazyTextFact where
  type FactDirection LazyTextFact = Souffle.InputOutput

  factName :: Proxy LazyTextFact -> String
  factName = const "string_fact"

instance Souffle.Fact Int32Fact where
  type FactDirection Int32Fact = Souffle.InputOutput

  factName :: Proxy Int32Fact -> String
  factName = const "number_fact"

instance Souffle.Fact Word32Fact where
  type FactDirection Word32Fact = Souffle.InputOutput

  factName :: Proxy Word32Fact -> String
  factName = const "unsigned_fact"

instance Souffle.Fact FloatFact where
  type FactDirection FloatFact = Souffle.InputOutput

  factName :: Proxy FloatFact -> String
  factName = const "float_fact"

instance Souffle.Fact NestedNewtype where
  type FactDirection NestedNewtype = Souffle.InputOutput

  factName :: Proxy NestedNewtype -> String
  factName = const "large_record"

instance Souffle.Fact NestedRecord where
  type FactDirection NestedRecord = Souffle.InputOutput

  factName :: Proxy NestedRecord -> String
  factName = const "large_record"

instance Souffle.Marshal StringFact
instance Souffle.Marshal TextFact
instance Souffle.Marshal LazyTextFact
instance Souffle.Marshal Int32Fact
instance Souffle.Marshal Word32Fact
instance Souffle.Marshal FloatFact

instance Souffle.Program RoundTrip where
  type ProgramFacts RoundTrip =
    [StringFact, TextFact, LazyTextFact, Int32Fact, Word32Fact, FloatFact, NestedNewtype, NestedRecord]

  programName :: RoundTrip -> String
  programName = const "round_trip"

type RoundTripAction
  = forall a. Souffle.Fact a
  => Souffle.ContainsInputFact RoundTrip a
  => Souffle.ContainsOutputFact RoundTrip a
  => Compiled.Submit a
  => Show a
  => a -> PropertyT IO a


data EdgeCases = EdgeCases

data EmptyStrings a
  = EmptyStrings a a Int32
  deriving stock (Eq, Show, Generic)

newtype LongStrings a
  = LongStrings a
  deriving stock (Eq, Show, Generic)

newtype Unicode a
  = Unicode a
  deriving stock (Eq, Show, Generic)

data NoStrings a = NoStrings Word32 Int32 Float
  deriving stock (Eq, Show, Generic)

instance Souffle.Program EdgeCases where
  type ProgramFacts EdgeCases =
    [ EmptyStrings String, EmptyStrings T.Text, EmptyStrings TL.Text
    , LongStrings String, LongStrings T.Text, LongStrings TL.Text
    , Unicode String, Unicode T.Text, Unicode TL.Text
    , NoStrings Void
    ]

  programName :: EdgeCases -> String
  programName = const "edge_cases"

instance Souffle.Fact (EmptyStrings String) where
  type FactDirection (EmptyStrings String) = Souffle.InputOutput
  factName = const "empty_strings"
instance Souffle.Fact (EmptyStrings T.Text) where
  type FactDirection (EmptyStrings T.Text) = Souffle.InputOutput
  factName = const "empty_strings"
instance Souffle.Fact (EmptyStrings TL.Text) where
  type FactDirection (EmptyStrings TL.Text) = Souffle.InputOutput
  factName = const "empty_strings"

instance Souffle.Fact (LongStrings String) where
  type FactDirection (LongStrings String) = Souffle.InputOutput
  factName = const "long_strings"
instance Souffle.Fact (LongStrings T.Text) where
  type FactDirection (LongStrings T.Text) = Souffle.InputOutput
  factName = const "long_strings"
instance Souffle.Fact (LongStrings TL.Text) where
  type FactDirection (LongStrings TL.Text) = Souffle.InputOutput
  factName = const "long_strings"

instance Souffle.Fact (Unicode String) where
  type FactDirection (Unicode String) = Souffle.InputOutput
  factName = const "unicode"
instance Souffle.Fact (Unicode T.Text) where
  type FactDirection (Unicode T.Text) = Souffle.InputOutput
  factName = const "unicode"
instance Souffle.Fact (Unicode TL.Text) where
  type FactDirection (Unicode TL.Text) = Souffle.InputOutput
  factName = const "unicode"

instance Souffle.Fact (NoStrings a) where
  type FactDirection (NoStrings _) = Souffle.InputOutput
  factName = const "no_strings"

instance Marshal (EmptyStrings String)
instance Marshal (EmptyStrings T.Text)
instance Marshal (EmptyStrings TL.Text)
instance Marshal (LongStrings String)
instance Marshal (LongStrings T.Text)
instance Marshal (LongStrings TL.Text)
instance Marshal (Unicode String)
instance Marshal (Unicode T.Text)
instance Marshal (Unicode TL.Text)
instance Marshal (NoStrings a)



spec :: Spec
spec = describe "Marshalling" $ parallel $ do
  describe "Auto-deriving marshalling code" $
    it "can generate code for all instances in this file" $
      -- If this file compiles, then the test has already passed
      42 `shouldBe` (42 :: Integer)

  roundTripSpecs
  edgeCaseSpecs

roundTripSpecs :: Spec
roundTripSpecs = describe "data transfer between Haskell and Souffle" $ parallel $ do
  let roundTripTests :: RoundTripAction -> Spec
      roundTripTests run = do
        it "can serialize and deserialize String values" $ hedgehog $ do
          str <- forAll $ Gen.string (Range.linear 0 10) Gen.unicode
          let fact = StringFact str
          fact' <- run fact
          fact === fact'

        it "can serialize and deserialize lazy Text values" $ hedgehog $ do
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

        it "can serialize and deserialize Float values" $ hedgehog $ do
          let epsilon = 1e-6
              fmin = -1e9
              fmax =  1e9
          x <- forAll $ Gen.float (Range.exponentialFloat fmin fmax)
          let fact = FloatFact x
          FloatFact x' <- run fact
          (abs (x' - x) < epsilon) === True

        it "can serialize and deserialize newtypes" $ hedgehog $ do
          a <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          b <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          c <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          d <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          let fact = NestedNewtype $ LargeRecord a b c d
          fact' <- run fact
          fact === fact'

        it "can serialize and deserialize nested product types" $ hedgehog $ do
          a <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          b <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          c <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          d <- forAll $ Gen.int32 (Range.linear minBound maxBound)
          let fact = NestedRecord (Pair a b) (Pair c d)
          fact' <- run fact
          fact === fact'


  describe "interpreted mode" $ parallel $
    roundTripTests $ \fact -> liftIO $ Interpreted.runSouffle RoundTrip $ \handle -> do
      let prog = fromJust handle
      Interpreted.addFact prog fact
      Interpreted.run prog
      Prelude.head <$> Interpreted.getFacts prog

  describe "compiled mode" $ parallel $
    roundTripTests $ \fact -> liftIO $ Compiled.runSouffle RoundTrip $ \handle -> do
      let prog = fromJust handle
      Compiled.addFact prog fact
      Compiled.run prog
      Prelude.head <$> Compiled.getFacts prog

edgeCaseSpecs :: Spec
edgeCaseSpecs = describe "edge cases" $ parallel $ do
  let longString :: IsString a => a
      longString = "long_string_from_DL:...............................................................................................................................................................................................................................................................................................end"

      getFactsI :: forall f a. (Souffle.Fact (f a), Souffle.ContainsOutputFact EdgeCases (f a)) => IO (List (f a))
      getFactsI = Interpreted.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Interpreted.run prog
        Interpreted.getFacts prog
      getFactsC :: forall f a. (Souffle.Fact (f a), Souffle.ContainsOutputFact EdgeCases (f a)) => IO (List (f a))
      getFactsC = Compiled.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Compiled.run prog
        Prelude.reverse <$> Compiled.getFacts prog

      getUnicodeFactsI :: forall a. (IsString a, Eq a, Souffle.Fact (Unicode a), Souffle.ContainsOutputFact EdgeCases (Unicode a))
                        => IO (Tuple3 (List (Unicode a)) (Maybe (Unicode a)) (Maybe (Unicode a)))
      getUnicodeFactsI = Interpreted.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Interpreted.run prog
        (,,) <$> Interpreted.getFacts prog
              <*> Interpreted.findFact prog (Unicode "⌀")  -- \x2300 iso \x2200
              <*> Interpreted.findFact prog (Unicode "≂")  -- \x2242 iso \x2200

      getUnicodeFactsC :: forall a. (IsString a, Eq a, Souffle.Fact (Unicode a), Souffle.ContainsOutputFact EdgeCases (Unicode a), Compiled.Submit (Unicode a))
                        => IO (Tuple3 (List (Unicode a)) (Maybe (Unicode a)) (Maybe (Unicode a)))
      getUnicodeFactsC = Compiled.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Compiled.run prog
        (,,) <$> (Prelude.reverse <$> Compiled.getFacts prog)
              <*> Compiled.findFact prog (Unicode "⌀")  -- \x2300 iso \x2200
              <*> Compiled.findFact prog (Unicode "≂")  -- \x2242 iso \x2200

      addAndGetFactsI :: Souffle.Fact (f a)
                      => Souffle.ContainsInputFact EdgeCases (f a)
                      => Souffle.ContainsOutputFact EdgeCases (f a)
                      => List (f a) -> IO (List (f a))
      addAndGetFactsI fs = Interpreted.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Interpreted.addFacts prog fs
        Interpreted.run prog
        Interpreted.getFacts prog
      addAndGetFactsC :: Souffle.Fact (f a)
                      => Souffle.ContainsInputFact EdgeCases (f a)
                      => Souffle.ContainsOutputFact EdgeCases (f a)
                      => Compiled.Submit (f a)
                      => List (f a) -> IO (List (f a))
      addAndGetFactsC fs = Compiled.runSouffle EdgeCases $ \handle -> do
        let prog = fromJust handle
        Compiled.addFacts prog fs
        Compiled.run prog
        Prelude.reverse <$> Compiled.getFacts prog


      runTests :: (forall f a. (Souffle.Fact (f a), Souffle.ContainsOutputFact EdgeCases (f a)) => IO (List (f a)))
                -> (forall a. (IsString a, Eq a, Souffle.Fact (Unicode a), Souffle.ContainsOutputFact EdgeCases (Unicode a), Compiled.Submit (Unicode a))
                    => IO (Tuple3 (List (Unicode a)) (Maybe (Unicode a)) (Maybe (Unicode a))))
                -> (forall f a. Souffle.Fact (f a)
                    => Souffle.ContainsInputFact EdgeCases (f a)
                    => Souffle.ContainsOutputFact EdgeCases (f a)
                    => Compiled.Submit (f a)
                    => List (f a) -> IO (List (f a)))
                -> Spec
      runTests getFacts getUnicodeFacts addAndGetFacts = do
        it "correctly marshals facts with number-like types" $ do
          facts <- getFacts
          (facts :: List (NoStrings Void))
            `shouldBe` [ NoStrings 42 (-100) 1.5
                       , NoStrings 123 (-456) 3.14
                       ]

        it "correctly marshals facts with empty Strings" $ do
          facts <- getFacts
          (facts :: List (EmptyStrings String))
            `shouldBe` [ EmptyStrings "" "" 42
                       , EmptyStrings "" "abc" 42
                       , EmptyStrings "abc" "" 42
                       ]

        it "correctly marshals facts with empty Texts" $ do
          facts <- getFacts
          (facts :: List (EmptyStrings T.Text))
            `shouldBe` [ EmptyStrings "" "" 42
                        , EmptyStrings "" "abc" 42
                        , EmptyStrings "abc" "" 42
                        ]

        it "correctly marshals facts with empty lazy Texts" $ do
          facts <- getFacts
          (facts :: List (EmptyStrings TL.Text))
            `shouldBe` [ EmptyStrings "" "" 42
                        , EmptyStrings "" "abc" 42
                        , EmptyStrings "abc" "" 42
                        ]

        it "correctly marshals facts really with long (>255 chars) String" $ do
          facts <- getFacts
          (facts :: List (LongStrings String)) `shouldBe` [ LongStrings longString ]

        it "correctly marshals facts really with long (>255 chars) Text" $ do
          facts <- getFacts
          (facts :: List (LongStrings T.Text)) `shouldBe` [ LongStrings longString ]

        it "correctly marshals facts really with long (>255 chars) lazy Text" $ do
          facts <- getFacts
          (facts :: List (LongStrings TL.Text)) `shouldBe` [ LongStrings longString ]

        it "correctly marshals facts containing unicode characters (String)" $ do
          results <- getUnicodeFacts
          results `shouldBe`
            ( [ Unicode ("∀" :: String), Unicode "∀∀" ]
            , Nothing :: Maybe (Unicode String)
            , Nothing :: Maybe (Unicode String)
            )

        it "correctly marshals facts containing unicode characters (Text)" $ do
          results <- getUnicodeFacts
          results `shouldBe`
            ( [ Unicode ("∀" :: T.Text), Unicode "∀∀" ]
            , Nothing :: Maybe (Unicode T.Text)
            , Nothing :: Maybe (Unicode T.Text)
            )

        it "correctly marshals facts containing unicode characters (lazy Text)" $ do
          results <- getUnicodeFacts
          results `shouldBe`
            ( [ Unicode ("∀" :: TL.Text), Unicode "∀∀" ]
            , Nothing :: Maybe (Unicode TL.Text)
            , Nothing :: Maybe (Unicode TL.Text)
            )

        it "correctly marshals empty strings back and forth (Strings)" $ do
          let facts :: List (EmptyStrings String)
              facts = [EmptyStrings "" "" 1, EmptyStrings "" "" 42, EmptyStrings "" "abc" 2, EmptyStrings "" "abc" 42, EmptyStrings "abc" "" 3, EmptyStrings "abc" "" 42]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals empty strings back and forth (Text)" $ do
          let facts :: List (EmptyStrings T.Text)
              facts = [EmptyStrings "" "" 1, EmptyStrings "" "" 42, EmptyStrings "" "abc" 2, EmptyStrings "" "abc" 42, EmptyStrings "abc" "" 3, EmptyStrings "abc" "" 42]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals empty strings back and forth (lazy Text)" $ do
          let facts :: List (EmptyStrings TL.Text)
              facts = [EmptyStrings "" "" 1, EmptyStrings "" "" 42, EmptyStrings "" "abc" 2, EmptyStrings "" "abc" 42, EmptyStrings "abc" "" 3, EmptyStrings "abc" "" 42]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals unicode back and forth (Strings)" $ do
          let facts :: List (Unicode String)
              facts = [Unicode "∀", Unicode "∀∀", Unicode "≂", Unicode "⌀", Unicode "⌀⌀"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals unicode back and forth (Text)" $ do
          let facts :: List (Unicode T.Text)
              facts = [Unicode "∀", Unicode "∀∀", Unicode "≂", Unicode "⌀", Unicode "⌀⌀"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals unicode back and forth (lazy Text)" $ do
          let facts :: List (Unicode TL.Text)
              facts = [Unicode "∀", Unicode "∀∀", Unicode "≂", Unicode "⌀", Unicode "⌀⌀"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals really long strings back and forth (Strings)" $ do
          let facts :: List (LongStrings String)
              facts = [LongStrings longString, LongStrings $ join $ Prelude.replicate 10000 "abc"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals really long strings back and forth (Text)" $ do
          let facts :: List (LongStrings T.Text)
              facts = [LongStrings longString, LongStrings $ T.pack $ join $ Prelude.replicate 10000 "abc"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals really long strings back and forth (lazy Text)" $ do
          let facts :: List (LongStrings TL.Text)
              facts = [LongStrings longString, LongStrings $ TL.pack $ join $ Prelude.replicate 10000 "abc"]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

        it "correctly marshals facts with number-like types" $ do
          let facts :: List (NoStrings Void)
              facts = [ NoStrings 42 (-100) 1.5
                      , NoStrings 123 (-456) 3.14
                      , NoStrings 789 (-789) 1000.123
                      , NoStrings 0x12345678 (-1000) 1234.56789
                      ]
          facts' <- addAndGetFacts facts
          facts' `shouldBe` facts

  describe "interpreted mode" $ parallel $ do
    runTests getFactsI getUnicodeFactsI addAndGetFactsI

  describe "compiled mode" $ parallel $ do
    runTests getFactsC getUnicodeFactsC addAndGetFactsC
