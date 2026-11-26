module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
/-- Every actual finite chain of original context deletions preserves both
source tests and equality of the unchanged computed evaluator. Intermediate
admission/equality is derived, never assumed. This is a family of internal
derivations indexed by external Nat, not a single arithmetic coded-trace law,
not equality of every arbitrary observer family, and not Object fixedness. -/
def ActualFiniteChain : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (steps : Nat)
 (left right parameter gamma : Fin (steps+1) → OTerm alpha)
 (count cutoff selectedType : Fin steps → OTerm alpha) (c : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (left 0) (right 0) (parameter 0))) →
 (∀ i : Fin steps, Nonempty (Derivation body Delta
   (DeletionChainDefinitions.Transition
     (left i.castSucc) (right i.castSucc) (left i.succ) (right i.succ)
     (parameter i.castSucc) (parameter i.succ) c (gamma i.castSucc) (gamma i.succ)
     (count i) (cutoff i) (selectedType i)))) →
 Nonempty (Derivation body Delta
   (AdmittedPair R H G M W (left (Fin.last steps)) (right (Fin.last steps)) (parameter (Fin.last steps))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainTargets
