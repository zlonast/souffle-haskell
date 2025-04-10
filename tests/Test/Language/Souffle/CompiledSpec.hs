module Test.Language.Souffle.CompiledSpec
  ( module Test.Language.Souffle.CompiledSpec
  ) where

import           Control.Applicative       (Applicative (..))

import qualified Data.Array                as A
import           Data.Bool                 (Bool (..))
import           Data.Eq                   (Eq)
import           Data.Foldable             (Foldable (..))
import           Data.Function             (const, ($))
import           Data.Functor              ((<$>))
import           Data.Int                  (Int)
import           Data.List                 (List)
import           Data.Maybe                (Maybe (..), fromJust, isJust)
import           Data.Monoid               (Monoid (..))
import           Data.Semigroup            (Semigroup (..))
import           Data.String               (String)
import qualified Data.Vector               as V

import           GHC.Generics              (Generic)

import qualified Language.Souffle.Compiled as Souffle

import           Test.Hspec                (Spec, describe, it, parallel, shouldBe)

import           Text.Show                 (Show)

data Path = Path

data Edge = Edge String String
  deriving stock (Eq, Show, Generic)

data Reachable = Reachable String String
  deriving stock (Eq, Show, Generic)

instance Souffle.Program Path where
  type ProgramFacts Path = [Edge, Reachable]

  programName :: Path -> String
  programName = const "path"

instance Souffle.Fact Edge where
  type FactDirection Edge = Souffle.InputOutput

  factName :: String
  factName = "edge"

instance Souffle.Fact Reachable where
  type FactDirection Reachable = Souffle.Output

  factName :: String
  factName = "reachable"

instance Souffle.Marshal Edge
instance Souffle.Marshal Reachable


data BadPath = BadPath

instance Souffle.Program BadPath where
  type ProgramFacts BadPath = [Edge, Reachable]

  programName :: BadPath -> String
  programName = const "bad_path"


spec :: Spec
spec = describe "Souffle API" $ parallel $ do
  describe "init" $ parallel $ do
    it "returns nothing in case it cannot load a souffle program" $ do
      prog <- Souffle.runSouffle BadPath pure
      isJust prog `shouldBe` False

    it "returns just the program in case it can load a souffle program" $ do
      prog <- Souffle.runSouffle Path pure
      isJust prog `shouldBe` True

  describe "getFacts" $ parallel $ do
    it "doesn't crash if used as last action (lists)" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` [Edge "b" "c", Edge "a" "b"]

    it "doesn't crash if used as last action (vectors)" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` V.fromList [Edge "a" "b", Edge "b" "c"]

    it "doesn't crash if used as last action (arrays)" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` A.listArray (0 :: Int, 1) [Edge "a" "b", Edge "b" "c"]

    it "can retrieve facts as a list" $ do
      (edges, reachables) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        es <- Souffle.getFacts prog
        rs <- Souffle.getFacts prog
        pure (es , rs)
      edges `shouldBe` [Edge "b" "c", Edge "a" "b"]
      reachables `shouldBe` [Reachable "b" "c", Reachable "a" "c", Reachable "a" "b"]

    it "can retrieve facts as a vector" $ do
      (edges, reachables) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        es <- Souffle.getFacts prog
        rs <- Souffle.getFacts prog
        pure (es , rs)
      edges `shouldBe` V.fromList [Edge "a" "b", Edge "b" "c"]
      reachables `shouldBe` V.fromList [Reachable "a" "b", Reachable "a" "c", Reachable "b" "c"]

    it "can retrieve facts as an array" $ do
      (edges, reachables) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        es <- Souffle.getFacts prog
        rs <- Souffle.getFacts prog
        pure (es , rs)
      edges `shouldBe` A.listArray (0 :: Int, 1) [Edge "a" "b", Edge "b" "c"]
      reachables `shouldBe` A.listArray (0 :: Int, 2) [Reachable "a" "b", Reachable "a" "c", Reachable "b" "c"]

    it "returns no facts in case program hasn't run yet" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.getFacts prog
      edges `shouldBe` ([] :: List Edge)

  describe "addFact" $ parallel $
    it "adds a fact" $ do
      (edgesBefore, edgesAfter) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        es1 <- Souffle.getFacts prog
        Souffle.addFact prog $ Edge "e" "f"
        Souffle.run prog
        es2 <- Souffle.getFacts prog
        pure (es1, es2)
      edgesBefore `shouldBe` [Edge "b" "c", Edge "a" "b"]
      edgesAfter `shouldBe` [Edge "e" "f", Edge "b" "c", Edge "a" "b"]

  describe "addFacts" $ parallel $
    it "can add multiple facts at once" $ do
      (edgesBefore, edgesAfter) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        es1 <- Souffle.getFacts prog
        Souffle.addFacts prog [Edge "e" "f", Edge "f" "g"]
        Souffle.run prog
        es2 <- Souffle.getFacts prog
        pure (es1, es2)
      edgesBefore `shouldBe` [Edge "b" "c", Edge "a" "b"]
      edgesAfter `shouldBe` [Edge "f" "g", Edge "e" "f", Edge "b" "c", Edge "a" "b"]

  describe "run" $ parallel $ do
    it "is OK to run a program multiple times" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` [Edge "b" "c", Edge "a" "b"]

    it "discovers new facts after running with new facts" $ do
      (reachablesBefore, reachablesAfter) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        rs1 <- Souffle.getFacts prog
        Souffle.addFacts prog [Edge "e" "f", Edge "f" "g"]
        Souffle.run prog
        rs2 <- Souffle.getFacts prog
        pure (rs1, rs2)
      reachablesBefore `shouldBe` [Reachable "b" "c", Reachable "a" "c", Reachable "a" "b"]
      reachablesAfter `shouldBe` [ Reachable "f" "g", Reachable "e" "g", Reachable "e" "f"
                                 , Reachable "b" "c",Reachable "a" "c", Reachable "a" "b" ]

  describe "configuring number of cores" $ parallel $
    it "is possible to configure number of cores" $ do
      results <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        numCpus1 <- Souffle.getNumThreads prog
        Souffle.setNumThreads prog 4
        numCpus2 <- Souffle.getNumThreads prog
        Souffle.setNumThreads prog 2
        numCpus3 <- Souffle.getNumThreads prog
        pure (numCpus1, numCpus2, numCpus3)
      results `shouldBe` (1, 4, 2)

  describe "findFact" $ parallel $ do
    it "returns Nothing in case no matching fact was found" $ do
      (edge, reachable) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        e <- Souffle.findFact prog $ Edge "c" "d"
        r <- Souffle.findFact prog $ Reachable "d" "e"
        pure (e, r)
      edge `shouldBe` Nothing
      reachable `shouldBe` Nothing

    it "returns Just the fact in case matching fact was found" $ do
      (edge, reachable) <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.run prog
        e <- Souffle.findFact prog $ Edge "a" "b"
        r <- Souffle.findFact prog $ Reachable "a" "c"
        pure (e, r)
      edge `shouldBe` Just (Edge "a" "b")
      reachable `shouldBe` Just (Reachable "a" "c")

    it "can handle unicode characters" $ do
      let fact = Edge "∀∀" "bla"
          fact2 = Edge "∃∃" "bla"
          fact3 = Edge "℀℀" "bla"
      results <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
        Souffle.addFact prog fact
        Souffle.run prog
        (,,) <$> Souffle.findFact prog fact
             <*> Souffle.findFact prog fact2
             <*> Souffle.findFact prog fact3
      results `shouldBe` (Just fact, Nothing, Nothing)

  -- TODO writeFiles / loadFiles

  describe "Semigroup and Monoid instances" $ parallel $ do
    it "combines Souffle actions into one using (<>)" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
            action1 = Souffle.addFact prog $ Edge "e" "f"
            action2 = Souffle.addFact prog $ Edge "f" "g"
            action = action1 <> action2
        action
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` [ Edge "f" "g", Edge "e" "f"
                       , Edge "b" "c", Edge "a" "b"
                       ]

    it "supports mempty" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
            action = Souffle.addFact prog $ Edge "e" "f"
            action' = action <> mempty
        action'
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` [Edge "e" "f", Edge "b" "c", Edge "a" "b"]

    it "supports foldMap" $ do
      edges <- Souffle.runSouffle Path $ \handle -> do
        let prog = fromJust handle
            fact1 = Edge "e" "f"
            fact2 = Edge "f" "g"
            action = foldMap (Souffle.addFact prog) [fact1, fact2]
        action
        Souffle.run prog
        Souffle.getFacts prog
      edges `shouldBe` [ Edge "f" "g", Edge "e" "f"
                       , Edge "b" "c", Edge "a" "b"
                       ]
