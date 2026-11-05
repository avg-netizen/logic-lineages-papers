module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupTargets
open NormalForm PlainLinearCleanup

def ExactLinearSelection : Prop := ∀ (p : Formula) (i : Nat),
  i ∈ linearNames p ↔ i ∈ p.variables ∧ LinearRows.isLinear i p = true

def ActualCleanupSemantics : Prop := ∀ (p : Formula) (ν : Nat → Nat),
  (cleanup p).eval ν ↔ existsPrefix ν (linearNames p) p

def ActualSatisfiabilityCleanup : Prop := ∀ p : Formula,
  Satisfiable (cleanup p) ↔ Satisfiable p

def ExactNonlinearNames : Prop := ∀ p : Formula,
  PlainBranchProvenance.nonlinearNames (cleanup p) = PlainBranchProvenance.nonlinearNames p

def NoLinearNames : Prop := ∀ (p : Formula) (i : Nat), i ∈ (cleanup p).variables →
  LinearRows.isLinear i (cleanup p) = false

def PreservePlain : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  MaximalPlainBranch.isPlain (cleanup p) = true

def GroundCriterion : Prop := ∀ p : Formula,
  PlainBranchProvenance.nonlinearNames p = ∅ → (cleanup p).variables = []

def LiteralCodeCalibration : Prop := ∀ p : Formula,
  Code.linearNames p.encode = linearNames p ∧ Code.cleanup p.encode = (cleanup p).encode

def ActualNumericPrograms : Prop := Primrec Code.linearNames ∧ Primrec Code.cleanup

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupTargets
