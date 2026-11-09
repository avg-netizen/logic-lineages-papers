module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphTargets
open ExpandedBooleanGraph

def LiteralForestSupport : Prop := ∀ (p : Matrix), (forest p).variables = p.variables
def HFreeOriginalForest : Prop := ∀ p : Matrix,
  PlainBlockSplit.matrixHFree p = true → PlainBlockSplit.termHFree (forest p) = true

def ActualPredicateInterpretation : Prop := ∀ (p : Matrix) (start : Nat) (ν : Nat → Nat),
  PlainBlockSplit.matrixHFree p = true →
  (ExpandedGraph.graph start (forest p)).eval ν →
    ((predicate start p).eval ν ↔ p.eval ν)

def ExactFreshGraphNames : Prop := ∀ (bound : List Nat) (p : Matrix),
  (allocated bound p).Nodup ∧
    (∀ i ∈ allocated bound p, i ∉ bound ∧ i ∉ p.variables)

def OriginalGraphNameSupport : Prop := ∀ (bound : List Nat) (p : Matrix) (j : Nat),
  j ∈ (compile bound p).variables → j ∈ p.variables ∨ j ∈ allocated bound p

/-- The output class needed by the literal bound-block initializer, stronger
than a test that merely allows arbitrary signed Phi shifts. -/
def LiteralZeroShiftGraphClass : Prop := ∀ (bound : List Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true → ∀ a ∈ LinearRows.atoms (compile bound p),
    ∀ entry ∈ a.row.2,
      (∃ i : Nat, entry.2 = NormalForm.Summand.variable i) ∨
      (∃ i : Nat, entry.2 = NormalForm.Summand.phi i 0)

def ActualExpandedMatrixGraph : Prop := ∀ (bound : List Nat) (p : Matrix) (ν : Nat → Nat),
  PlainBlockSplit.matrixHFree p = true →
    (NormalForm.existsPrefix ν (allocated bound p) (compile bound p) ↔ p.eval ν)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphTargets
