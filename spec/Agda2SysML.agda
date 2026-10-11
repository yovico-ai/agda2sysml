{-# OPTIONS --safe #-}
module Agda2SysML where

import Agda2SysML.Foundation
import Agda2SysML.Resolution
import Agda2SysML.Mapping
import Agda2SysML.DecisionTree
import Agda2SysML.Relations
import Agda2SysML.Coverage
import Agda2SysML.Obligations
import Agda2SysML.Provenance
import Agda2SysML.Terms
import Agda2SysML.Sharing

import Agda2SysML.BooleanLowering

import Agda2SysML.DependentFamilies

import Agda2SysML.FiniteLowering

import Agda2SysML.AlgebraicValues
import Agda2SysML.StructuredIndices
import Agda2SysML.SchemaConcatenation
import Agda2SysML.NaturalValues
import Agda2SysML.NaturalIndices
import Agda2SysML.SequenceValues
import Agda2SysML.RecursiveCalls
import Agda2SysML.RecursiveValues
import Agda2SysML.FirstOrder
import Agda2SysML.Specialization
import Agda2SysML.OpenParameters
import Agda2SysML.FamilyRelations
import Agda2SysML.UniverseLevels
import Agda2SysML.IndexedValues
import Agda2SysML.DependentRecords
import Agda2SysML.SpecializedFamilies
import Agda2SysML.DependentSums
import Agda2SysML.ComputedIndices
import Agda2SysML.RelationBindings
import Agda2SysML.Diagnostics
import Agda2SysML.SourceOccurrences

open import Agda2SysML.Derivations
import Agda2SysML.SourceAlignment

import Agda2SysML.DefinitionalReduction

import Agda2SysML.DependencyScope

import Agda2SysML.DeclarationSelection

import Agda2SysML.CapturedIndices
