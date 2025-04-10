module Main (main) where

import           Control.Applicative       (Applicative (..))
import           Control.DeepSeq           (NFData)
import           Control.Monad             (replicateM_)
import           Control.Monad.IO.Class    (MonadIO (..))

import           Criterion.Main            (Benchmark, bench, bgroup, defaultMain, nfIO)

import           Data.Function             (const, ($))
import           Data.Int                  (Int, Int32)
import           Data.List                 (List, (++))
import           Data.Maybe                (Maybe (..))
import           Data.Proxy                (Proxy)
import           Data.String               (String)
import qualified Data.Text                 as T
import qualified Data.Vector               as V
import           Data.Word                 (Word32)

import           GHC.Float                 (Float)
import           GHC.Generics              (Generic)
import           GHC.Real                  (fromIntegral)
import           GHC.Tuple                 (Unit)

import qualified Language.Souffle.Compiled as S

import           System.IO                 (IO, putStrLn)


data Benchmarks = Benchmarks

data NumbersFact
  = NumbersFact Word32 Int32 Float
  deriving stock (Generic)
  deriving anyclass (NFData)

data StringsFact
  = StringsFact Word32 T.Text Int32 Float
  deriving stock (Generic)
  deriving anyclass (NFData)

newtype FromDatalogFact
  = FromDatalogFact Int32
  deriving stock (Generic)
  deriving anyclass (NFData)

data FromDatalogStringFact
  = FromDatalogStringFact Int32 T.Text
  deriving stock (Generic)
  deriving anyclass (NFData)

instance S.Program Benchmarks where
  type ProgramFacts Benchmarks = [NumbersFact, StringsFact, FromDatalogFact, FromDatalogStringFact]

  programName :: Benchmarks -> String
  programName = const "bench"

instance S.Fact NumbersFact where
  type FactDirection NumbersFact = 'S.InputOutput

  factName :: Proxy NumbersFact -> String
  factName = const "numbers_fact"

instance S.Fact StringsFact where
  type FactDirection StringsFact = 'S.InputOutput

  factName :: Proxy StringsFact -> String
  factName = const "strings_fact"

instance S.Fact FromDatalogFact where
  type FactDirection FromDatalogFact = 'S.InputOutput

  factName :: Proxy FromDatalogFact -> String
  factName = const "from_datalog_fact"

instance S.Fact FromDatalogStringFact where
  type FactDirection FromDatalogStringFact = 'S.InputOutput

  factName :: Proxy FromDatalogStringFact -> String
  factName = const "from_datalog_string_fact"

instance S.Marshal NumbersFact
instance S.Marshal StringsFact
instance S.Marshal FromDatalogFact
instance S.Marshal FromDatalogStringFact

-- TODO: fix cases with larger numbers (crashes due to large memory allocations?)
main :: IO Unit
main = defaultMain
     $ roundTripBenchmarks
    ++ serializationBenchmarks
    ++ deserializationBenchmarks

roundTripBenchmarks :: List Benchmark
roundTripBenchmarks =
  [ bgroup "round trip facts (without strings)"
    [ bench "1"      $ nfIO $ roundTrip $ mkVec 1
    , bench "10"     $ nfIO $ roundTrip $ mkVec 10
    , bench "100"    $ nfIO $ roundTrip $ mkVec 100
    , bench "1000"   $ nfIO $ roundTrip $ mkVec 1000
    , bench "10000"  $ nfIO $ roundTrip $ mkVec 10000
    --, bench "100000" $ nfIO $ roundTrip $ mkVec 100000
    ]
  , bgroup "round trip facts (with strings)"
    [ bench "1"      $ nfIO $ roundTrip $ mkVecStr 1
    , bench "10"     $ nfIO $ roundTrip $ mkVecStr 10
    , bench "100"    $ nfIO $ roundTrip $ mkVecStr 100
    , bench "1000"   $ nfIO $ roundTrip $ mkVecStr 1000
    --, bench "10000"  $ nfIO $ roundTrip $ mkVecStr 10000
    --, bench "100000" $ nfIO $ roundTrip $ mkVecStr 100000
    ]
  , bgroup "round trip facts (with long strings)"
    [ bench "1"      $ nfIO $ roundTrip $ mkVecLongStr 1
    , bench "10"     $ nfIO $ roundTrip $ mkVecLongStr 10
    , bench "100"    $ nfIO $ roundTrip $ mkVecLongStr 100
    --, bench "1000"   $ nfIO $ roundTrip $ mkVecLongStr 1000
    --, bench "10000"  $ nfIO $ roundTrip $ mkVecLongStr 10000
    --, bench "100000" $ nfIO $ roundTrip $ mkVecLongStr 100000
    ]
  ]
  where mkVec count = V.generate count $ \i -> NumbersFact (fromIntegral i) (-42) 3.14
        mkVecStr count = V.generate count $ \i -> StringsFact (fromIntegral i) "abcdef" (-42) 3.14
        mkVecLongStr count = V.generate count $ \i -> StringsFact (fromIntegral i) (T.replicate 10 "abcdef") (-42) 3.14

roundTrip :: (S.ContainsInputFact Benchmarks a, S.ContainsOutputFact Benchmarks a, S.Fact a, S.Submit a)
          => V.Vector a -> IO (V.Vector a)
roundTrip vec = S.runSouffle Benchmarks $ \case
  Nothing -> do
    liftIO $ putStrLn "Failed to load roundtrip benchmarks!"
    pure V.empty
  Just prog -> do
    S.addFacts prog vec
    -- No run needed
    S.getFacts prog


serializeNumbers :: Int -> IO Unit
serializeNumbers iterationCount = S.runSouffle Benchmarks $ \case
  Nothing -> liftIO $ putStrLn "Failed to load serialize benchmarks!"
  Just prog ->
    replicateM_ iterationCount $ S.addFacts prog vec
    -- No run needed
  where vec = V.generate 100 $ \i -> NumbersFact (fromIntegral i) (-42) 3.14

deserializeNumbers :: Int -> IO Unit
deserializeNumbers iterationCount = S.runSouffle Benchmarks $ \case
  Nothing -> liftIO $ putStrLn "Failed to load deserialize benchmarks!"
  Just prog -> do
    S.run prog
    replicateM_ iterationCount $ do
      fs <- S.getFacts prog
      pure (fs :: V.Vector FromDatalogFact)

serializeWithStrings :: Int -> IO Unit
serializeWithStrings iterationCount = S.runSouffle Benchmarks $ \case
  Nothing -> liftIO $ putStrLn "Failed to load serialize benchmarks!"
  Just prog ->
    replicateM_ iterationCount $ S.addFacts prog vec
    -- No run needed
  where vec = V.generate 100 $ \i -> StringsFact (fromIntegral i) "abcdef" (-42) 3.14

deserializeWithStrings :: Int -> IO Unit
deserializeWithStrings iterationCount = S.runSouffle Benchmarks $ \case
  Nothing -> liftIO $ putStrLn "Failed to load deserialize benchmarks!"
  Just prog -> do
    S.run prog
    replicateM_ iterationCount $ do
      fs <- S.getFacts prog
      pure (fs :: V.Vector FromDatalogStringFact)

serializationBenchmarks :: List Benchmark
serializationBenchmarks =
  [ bgroup "serializing facts (without strings)"
    [ bench "1"      $ nfIO $ serializeNumbers 1
    , bench "10"     $ nfIO $ serializeNumbers 10
    , bench "100"    $ nfIO $ serializeNumbers 100
    , bench "1000"   $ nfIO $ serializeNumbers 1000
    , bench "10000"  $ nfIO $ serializeNumbers 10000
    ]
  , bgroup "serializing facts (with strings)"
    [ bench "1"      $ nfIO $ serializeWithStrings 1
    , bench "10"     $ nfIO $ serializeWithStrings 10
    , bench "100"    $ nfIO $ serializeWithStrings 100
    , bench "1000"   $ nfIO $ serializeWithStrings 1000
    , bench "10000"  $ nfIO $ serializeWithStrings 10000
    ]
  ]

deserializationBenchmarks :: List Benchmark
deserializationBenchmarks =
  [ bgroup "deserializing facts (without strings)"
    [ bench "1"      $ nfIO $ deserializeNumbers 1
    , bench "10"     $ nfIO $ deserializeNumbers 10
    , bench "100"    $ nfIO $ deserializeNumbers 100
    , bench "1000"   $ nfIO $ deserializeNumbers 1000
    , bench "10000"  $ nfIO $ deserializeNumbers 10000
    ]
  , bgroup "deserializing facts (with strings)"
    [ bench "1"      $ nfIO $ deserializeWithStrings 1
    , bench "10"     $ nfIO $ deserializeWithStrings 10
    , bench "100"    $ nfIO $ deserializeWithStrings 100
    , bench "1000"   $ nfIO $ deserializeWithStrings 1000
    , bench "10000"  $ nfIO $ deserializeWithStrings 10000
    ]
  ]
