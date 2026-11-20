module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets
open NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof (Ready)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consOfGraph (p q : Program 3) (h t : OTerm α) (xs : Fin 3 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph p h xs)))
    (right : Nonempty (Derivation body Γ (programGraph q t xs))) :
    Nonempty (Derivation body Γ (programGraph (consOf p q) (rawCons h t) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0)) (rawCons h t) xs ![h,t]
    (consGraph h t)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

theorem emit (xs : Fin 3 → OTerm α) (src child dst : OTerm α)
    (facts : Ready body Γ xs src child dst) :
    Nonempty (Derivation body Γ (programGraph emitFrame (frameValueTerm src child dst) xs)) := by
  let a := consOf (frameSlot 2 2) (constantZero 3)
  let b := consOf (frameSlot 0 1) a
  let c := consOf (frameSlot 2 0) b
  let ta := rawCons dst z
  let tb := rawCons child ta
  let tc := rawCons src tb
  have ha : Nonempty (Derivation body Γ (programGraph a ta xs)) :=
    consOfGraph (frameSlot 2 2) (constantZero 3) dst z xs facts.target (constantZeroValue xs)
  have hb : Nonempty (Derivation body Γ (programGraph b tb xs)) :=
    consOfGraph (frameSlot 0 1) a child ta xs facts.witness ha
  have hc : Nonempty (Derivation body Γ (programGraph c tc xs)) :=
    consOfGraph (frameSlot 2 0) b src tb xs facts.source hb
  unfold emitFrame frameValueTerm
  apply compositionValue .succ (fun _ : Fin 1 => c) (suc tc) xs ![tc] (successorValue ![tc])
  intro k
  obtain rfl := Fin.eq_zero k
  exact hc

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof
