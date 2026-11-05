module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitTargets
open NormalForm PlainBranchSplit PlainLinearCleanup

def GroundSmall : Prop := ∀ p : Formula, (small p).variables = []

def ActualSmallEvaluation : Prop := ∀ p : Formula, smallAnswer p = true ↔ Satisfiable (small p)

def SmallSoundness : Prop := ∀ p : Formula, Satisfiable (small p) → Satisfiable p

def BranchSoundness : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  ∀ q ∈ branches p, Satisfiable q → Satisfiable p

/-- Coverage is derived from a maximum of the actual finite original name list,
not assumed as an external exhaustive-cases hypothesis. -/
def ExhaustiveCoverage : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  (Satisfiable p ↔ smallAnswer p = true ∨ ∃ q ∈ branches p, Satisfiable q)

def ActualStep : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  (Satisfiable p ↔ (step p).1 = true ∨ ∃ q ∈ (step p).2, Satisfiable q)

def StrictFrontierDecrease : Prop := ∀ (p q : Formula), q ∈ (step p).2 →
  (PlainBranchProvenance.nonlinearNames q).card < (PlainBranchProvenance.nonlinearNames p).card

def PreservePlain : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  ∀ q ∈ (step p).2, MaximalPlainBranch.isPlain q = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitTargets
