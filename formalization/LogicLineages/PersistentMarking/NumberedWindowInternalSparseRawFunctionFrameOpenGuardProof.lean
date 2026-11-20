module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports witnessReports onTape)

abbrev liftedTape {α : Type} (dom cod arg src child dst : OTerm α) : Fin 3 → OTerm α :=
  ![auxiliaryTerm dom cod src arg,functionWitnessTerm child,auxiliaryTerm dom cod dst arg]

structure Ready {α : Type} (body : Positive (Fin 1)) (Γ : List (Formula α))
    (xs : Fin 3 → OTerm α) (src child dst : OTerm α) : Prop where
  guard : Nonempty (Derivation body Γ (programGraph frameGood (suc z) xs))
  source : Nonempty (Derivation body Γ (programGraph (frameSlot 2 0) src xs))
  witness : Nonempty (Derivation body Γ (programGraph (frameSlot 0 1) child xs))
  target : Nonempty (Derivation body Γ (programGraph (frameSlot 2 2) dst xs))

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem equalSlot (n : Nat) (v : OTerm α) (xs : Fin 3 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph (frameSlot n 0) v xs)))
    (right : Nonempty (Derivation body Γ (programGraph (frameSlot n 2) v xs))) :
    Nonempty (Derivation body Γ (programGraph (sameSlot n) (suc z) xs)) := by
  unfold sameSlot
  apply compositionValue equalityTest ![frameSlot n 0,frameSlot n 2] (suc z) xs ![v,v] (equalitySelf v)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

theorem literalTape (dom cod arg src child dst : OTerm α) :
    Ready body Γ (liftedTape dom cod arg src child dst) src child dst := by
  let xs := liftedTape dom cod arg src child dst
  obtain ⟨left,L⟩ := termReports (body := body) (Γ := Γ) dom cod src arg
  obtain ⟨right,R⟩ := termReports (body := body) (Γ := Γ) dom cod dst arg
  obtain ⟨middle,W⟩ := witnessReports (body := body) (Γ := Γ) child
  have hd := equalSlot 0 dom xs (onTape (field 0) 0 dom xs L.1) (onTape (field 0) 2 dom xs R.1)
  have ht := equalSlot 1 cod xs (onTape (field 1) 0 cod xs L.2.1) (onTape (field 1) 2 cod xs R.2.1)
  have ha := equalSlot 3 arg xs (onTape (field 3) 0 arg xs L.2.2.2.1)
    (onTape (field 3) 2 arg xs R.2.2.2.1)
  have hf : Nonempty (Derivation body Γ (programGraph frameGood (suc z) xs)) :=
    conjunctionAccept (onRaw witnessShape 1) _ xs (onTape witnessShape 1 (suc z) xs middle)
      (conjunctionAccept (onRaw termShape 0) _ xs (onTape termShape 0 (suc z) xs left)
        (conjunctionAccept (onRaw termShape 2) _ xs (onTape termShape 2 (suc z) xs right)
          (conjunctionAccept (sameSlot 0) _ xs hd (conjunctionAccept (sameSlot 1) (sameSlot 3) xs ht ha))))
  exact ⟨hf,onTape (field 2) 0 src xs L.2.2.1,onTape (field 0) 1 child xs W.1,
    onTape (field 2) 2 dst xs R.2.2.1⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof
