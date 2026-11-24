module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape rawSourceCheck observePartition)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets scratchTargets)
open NumberedWindowInternalDirectInsertedScanTargets (scan loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)

structure Reports (sourceObserver targetObserver : Program 2) (r : Program 3)
    (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (source target kept removed inserted s t k d a p sk tp : OTerm α) : Prop where
  sourceParsed : Nonempty (Derivation B Γ (unary parser (suc s) source))
  targetParsed : Nonempty (Derivation B Γ (unary parser (suc t) target))
  keptParsed : Nonempty (Derivation B Γ (unary parser (suc k) kept))
  removedParsed : Nonempty (Derivation B Γ (unary parser (suc d) removed))
  insertedParsed : Nonempty (Derivation B Γ (unary parser (suc a) inserted))
  rawProjection : Nonempty (Derivation B Γ (unary insertedTargets (suc p) inserted))
  scratchProjection : Nonempty (Derivation B Γ (unary scratchTargets (suc p) a))
  sourceAppend : Nonempty (Derivation B Γ (programGraph append sk ![k,d]))
  targetAppend : Nonempty (Derivation B Γ (programGraph append tp ![k,p]))
  sourceObserved : Nonempty (Derivation B Γ (programGraph sourceObserver (suc z) ![s,sk]))
  targetObserved : Nonempty (Derivation B Γ (programGraph targetObserver (suc z) ![t,tp]))
  scanObserved : Nonempty (Derivation B Γ (loopAccept r a removed))

/-- One common scratch tuple from the actual component-one graph reports.
The scan's parser input is the target-side actual inserted parser value,
and both appends share the source-side actual kept parser value. -/
def ExactOpenSharedTape : Prop :=
  ∀ (sourceObserver targetObserver : Program 2) (r : Program 3)
      (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (source target kept removed inserted : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (rawSourceCheck (observePartition sourceObserver))
      (suc z) (sourceTape source kept removed))) →
    Nonempty (Derivation B Γ (programGraph (rawTargetCheck targetObserver)
      (suc z) (sourceTape target kept inserted))) →
    Nonempty (Derivation B Γ (programGraph (scan r) oneTerm ![inserted,removed])) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (s t k d a p sk tp : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports sourceObserver targetObserver r B Δ (source.relabel j) (target.relabel j)
        (kept.relabel j) (removed.relabel j) (inserted.relabel j) s t k d a p sk tp →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
