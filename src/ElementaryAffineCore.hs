{-# LANGUAGE DataKinds, ExplicitNamespaces #-}

-- |
-- Module      : ElementaryAffineCore
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Main module for the parser. It reexports useful types from the
-- internal modules and contains the function which launches sequentially
-- 3 parts of parsing of Elementary Affine Core:
-- 1) Parsing
-- 2) Checking stratification rules
-- 3) Substitute local definitions by their bodies + rename variables

module ElementaryAffineCore (Exp(..), Exps(..), type Term,type ParsedCore,
    ParsedCoreError(..), StratificationRule (..), StratificationRuleBroken(..),
    type WarningInfo, Warning (..), parseElementaryAffineCore) where

import Control.Monad.Writer (Writer)
import Control.Monad.Except (ExceptT(..), lift, throwError, withExceptT)
import Control.Monad.Morph (generalize, hoist)
import Data.Text (Text, pack)
import Text.Megaparsec (SourcePos(..), runParser, errorBundlePretty)

import qualified Data.Map as M

import ElementaryAffineCore.Parser
import ElementaryAffineCore.Types hiding (Expression(..), Exps, Term)
import qualified ElementaryAffineCore.Types as T (Expression(..), Exps(..), Term(..))
import ElementaryAffineCore.StratificationChecker
import ElementaryAffineCore.Substitutor

type Term = T.Term 'Final
type Exps = T.Exps 'Final
type ParsedCore = ExceptT ParsedCoreError (Writer [WarningInfo]) Exps
data ParsedCoreError = StratruleBroken StratificationRuleBroken | ParseError Text deriving Show

-- | Runs parser, checks stratification rules and substitutes local definitions.
parseElementaryAffineCore :: FilePath -> Text -> ParsedCore
parseElementaryAffineCore filename text = case runParser topExpressions filename text of
    Left errBundle -> throwError $ ParseError $ pack $ errorBundlePretty errBundle
    Right topExpressions -> do
            hoist generalize $ withExceptT StratruleBroken $ mapM checkExp topExpressions
            lift $ substituteLocalExps topExpressions

