module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationTargets
open OriginalSourceElimination CommonLayerSyntax

def LiteralBaseEmbedding : Prop := ∀ a : BaseTerm,
  (∀ ν : Nat → Nat, (embed a).value ν = a.value ν) ∧
    (embed a).variables = a.variables ∧ PlainBlockSplit.termHFree (embed a) = true

def ExactBinderBlock : Prop := ∀ (i : Nat) (p : Matrix), (binderBlock i p).Nodup

def LiteralBinderInputClass : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true →
    WholeBoundInitialization.ZeroShift (graphFormula i p)

def ActualBinderElimination : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true → ∀ ν : Nat → Nat,
    ((eliminateBinder i p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν i n))

def OriginalBinderNameSupport : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true → ∀ j ∈ (eliminateBinder i p).variables,
    j ≠ i ∧ j ∈ p.variables

def HFreeBinderOutput : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true →
    PlainBlockSplit.matrixHFree (eliminateBinder i p) = true

/-- All original source formulas and valuations, with no source-shape premise.
This typed equivalence is not an effective-elimination assertion. -/
def ActualSourceElimination : Prop := ∀ (p : SourceFormula) (ν : Nat → Nat),
  (eliminate p).eval ν ↔ p.eval ν

def OriginalSourceNameSupport : Prop := ∀ (p : SourceFormula) (i : Nat),
  i ∈ (eliminate p).variables → i ∈ p.variables

def HFreeSourceOutput : Prop := ∀ p : SourceFormula,
  PlainBlockSplit.matrixHFree (eliminate p) = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationTargets
