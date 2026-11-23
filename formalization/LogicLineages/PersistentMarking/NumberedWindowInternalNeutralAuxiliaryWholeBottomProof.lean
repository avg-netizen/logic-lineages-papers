module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryWholeBottomProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAtomicRefinement (bottomTarget bottomOf bottomEmitter atSource)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm sourceFields)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (bottomEmitterGraph)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem reportBottom (x c t : OTerm α)
    (h : Nonempty (Derivation B Γ (sourceFields x c t))) :
    Nonempty (Derivation B Γ (programGraph bottomOf (packedBottomTerm c t) ![x])) := by
  obtain ⟨f⟩ := h
  have hc : Nonempty (Derivation B Γ (programGraph rawContext c ![x])) :=
    ⟨Derivation.conjunctionLeft f⟩
  have ht : Nonempty (Derivation B Γ (programGraph rawResult t ![x])) :=
    ⟨Derivation.conjunctionRight f⟩
  unfold bottomOf
  apply compositionValue bottomEmitter (Fin.cons rawContext (Fin.cons rawResult Fin.elim0))
    (packedBottomTerm c t) ![x] ![c,t] (bottomEmitterGraph c t)
  intro k
  exact Fin.cases hc (Fin.cases ht (fun j => Fin.elim0 j)) k

/-- The actual original comparator accepts only the exact literal
whole bottom at the real source context and result type. Applicable
to the new free-headed branch without assuming the old bottom shape. -/
theorem exact_OpenNeutralWholeBottom (x w y c t : OTerm α)
    (fields : Nonempty (Derivation B Γ (sourceFields x c t)))
    (held : Nonempty (Derivation B Γ (programGraph bottomTarget (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (equal y (packedBottomTerm c t))) := by
  let xs : Fin 3 → OTerm α := ![x,w,y]
  let b := packedBottomTerm c t
  let ps : Fin 2 → Program 3 := Fin.cons (.projection (2 : Fin 3)) (Fin.cons (atSource bottomOf) Fin.elim0)
  have new : Nonempty (Derivation B Γ (programGraph (atSource bottomOf) b xs)) :=
    callSlot bottomOf 0 b xs (reportBottom x c t fields)
  have tested := compositionRecover compareNumbers ps (suc z) xs ![y,b] held
    (fun j => Fin.cases (projectionValue (2 : Fin 3) xs) (Fin.cases new (fun k => Fin.elim0 k)) j)
  rw [exact_DispatchControlAST.2.2.2.1] at tested
  rw [equalEqn]
  exact equalityOfAcceptance y b tested

#print axioms exact_OpenNeutralWholeBottom
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryWholeBottomProof
