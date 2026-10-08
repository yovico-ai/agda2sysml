{-# LANGUAGE OverloadedStrings, LambdaCase #-}
-- | Recover source locations separately from the checked interface: Agda drops
-- clause ranges when constructing interfaces, even during a fresh check.
module Agda2SysML.Source (sourceSyntax, sourceInfo, location) where

import qualified Agda2SysML.SourceCatalog as Catalog
import Agda.Compiler.Backend (TCM, runPM)
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as N
import Agda.Syntax.Parser (parseFile, moduleParser)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (ScopeInfo(..))
import Agda.Syntax.Common.Pretty (prettyShow)
import Data.Aeson
import Data.Text (Text)

location :: Range -> Value
location = Catalog.navigation

sourceSyntax :: ScopeInfo -> RangeFile -> String -> TCM Value
sourceSyntax scope file contents = fst <$> sourceInfo scope file contents

sourceInfo :: ScopeInfo -> RangeFile -> String -> TCM (Value, [Catalog.SyntaxNode])
sourceInfo scope file contents = do
  ((parsed,_),_) <- runPM (parseFile moduleParser file contents)
  pure (object ["functions" .= collect C.NoWhere_ (C.modDecls parsed)], Catalog.collect scope (C.modDecls parsed))
  where
    collect context declarations = case fst $ N.runNice (N.NiceEnv False context) $
      N.niceDeclarations (_scopeFixities scope) declarations of
        Left _ -> [object ["unavailable" .= ("source-grouping-unavailable" :: Text), "source" .= location (getRange declarations)]]
        Right nice -> concatMap visit nice
    visit = \case
      N.NiceModule _ _ _ _ _ _ ds -> collect C.NoWhere_ ds
      N.NiceMutual _ _ _ _ ds -> concatMap visit ds
      N.NiceOpaque _ _ ds -> concatMap visit ds
      N.NiceRecDef _ _ _ _ _ _ _ _ ds -> collect C.NoWhere_ ds
      N.FunDef r _ _ _ _ _ n clauses -> object
        ["name" .= prettyShow n, "binding" .= location (getRange n), "source" .= location r
        ,"clauses" .= map sourceClause clauses] : concatMap local clauses
      N.NiceFunClause r _ _ _ _ _ _ -> [object
        ["unavailable" .= ("An inferred local definition has no explicit signature anchor" :: Text), "source" .= location r]]
      _ -> []
    sourceClause (N.Clause _ _ lhs rhs wh children) = object
      ["source" .= location (getRange lhs `fuseRange` rhs `fuseRange` wh)
      ,"lhs" .= location (getRange lhs), "rhs" .= location (getRange rhs)
      ,"withClauses" .= map sourceClause children]
    local (N.Clause _ _ _ _ wh children) = whereDeclarations wh ++ concatMap local children
    whereDeclarations wh = case wh of
      C.NoWhere -> []
      C.AnyWhere _ ds -> collect (C.whereClause_ wh) ds
      C.SomeWhere _ _ _ _ ds -> collect (C.whereClause_ wh) ds
