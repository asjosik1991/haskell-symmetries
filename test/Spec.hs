module Main where

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
import MyLib
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

--function to initialize a graph from lists
graph :: (Ord t) => ([t], [[t]]) -> Graph t
graph (vs,es) = G (S.fromList vs) (S.fromList (map S.fromList es))

-- |c n is the cyclic graph on n vertices
c :: (Integral t) => t -> Graph t
c n | n >= 3 = graph (vs,es) where
    vs = [1..n]
    es = L.insert [1,n] [[i,i+1] | i <- [1..n-1]]
-- automorphism group   is D2n

main :: IO ()
main = hspec $ do
  describe "MyLib.hs" $ do
    it "the number of automorphisms for cyclic graphs" $ do
      map (length.eltsSGS.graphAuts.c) [3,4,11,20] `shouldBe` ([6,8,22,40] :: [Int])
