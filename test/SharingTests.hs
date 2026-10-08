{-# LANGUAGE OverloadedStrings #-}
module Main (main) where
import Agda2SysML.Sharing
import Control.Monad (unless)
import Control.Monad.State.Strict (runState)
import Data.Aeson
import qualified Data.Aeson.Key as K
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Vector as V
import Test.QuickCheck

newtype Tree = Tree Value deriving Show
instance Arbitrary Tree where
  arbitrary = sized (fmap Tree . tree)
    where
      tree 0 = oneof [pure Null, Bool <$> arbitrary, String . T.pack <$> arbitrary, toJSON <$> (arbitrary :: Gen Integer)]
      tree n = frequency [(3,tree 0), (1,Array . V.fromList <$> resize 4 (listOf (tree (n `div` 3))))
        ,(1,object <$> resize 4 (listOf ((.=) <$> key <*> tree (n `div` 3))))]
      key = K.fromText <$> elements ["tag","$node","object","array","λ","value"]

roundtrip :: Tree -> Property
roundtrip (Tree value) = conjoin [property (expand table packed == Right value)
  ,property (expand collisionTable collisionPacked == Right value)]
  where
    (packed,table) = runState (intern value) emptyNodes
    (collisionPacked,collisionTable) = runState (internWith (const "collision") value) emptyNodes

main :: IO ()
main = do
  result <- quickCheckWithResult stdArgs {maxSuccess = 500, maxSize = 30} roundtrip
  unless (isSuccess result) (fail "shared-term reconstruction failed")
  let reference = object ["$node" .= ("self" :: T.Text)]
      cycleTable = M.singleton "self" (object ["array" .= [reference]])
  unless (expand cycleTable reference == Left "cyclic shared term") $ fail "cycle accepted"
  unless (expand M.empty reference == Left "missing shared term") $ fail "missing reference accepted"
  let x = object ["x" .= (42 :: Int)]
      (packed,table) = runState (intern (toJSON [x,x])) emptyNodes
  unless (M.size table == 2 && expand table packed == Right (toJSON [x,x])) $ fail "identical subtrees were not shared"
