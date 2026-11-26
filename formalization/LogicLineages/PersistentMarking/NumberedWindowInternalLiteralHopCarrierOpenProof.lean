module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph)
open NumberedWindowInternalLiteralHopCarrier

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem slotCall (p : Program 1) (k : Fin 5) (xs : Fin 5 → OTerm α)
    (h : D B Γ (unary p (suc z) (xs k))) :
    D B Γ (programGraph (atSlot p k) (suc z) xs) := by
  apply compositionValue p ![.projection k] (suc z) xs ![xs k] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue k xs

private theorem packedLeastGraph (L : Program 3) (ctx ty q w r k : OTerm α)
    (h : D B Γ (programGraph L (suc k) ![ctx,ty,r])) :
    D B Γ (programGraph (targetLeast L) (suc k) ![ctx,ty,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  apply compositionValue L ![.projection 0,.projection 1,.projection 4] (suc k) xs ![ctx,ty,r] h
  intro j
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 4 xs) (fun e => Fin.elim0 e))) j

private theorem packedAddressGraph (L : Program 3) (ctx ty q w r k : OTerm α)
    (held : D B Γ (programGraph (targetLeast L) (suc k) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (targetAddress L) (addressTerm ctx ty k) ![ctx,ty,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  have pred : D B Γ (unary predOne k (suc k)) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor k
  have off : D B Γ (programGraph (targetCode L) k xs) := by
    apply compositionValue predOne ![targetLeast L] k xs ![suc k] pred
    intro a
    obtain rfl := Fin.eq_zero a
    exact held
  apply compositionValue addressEmitter ![.projection 0,.projection 1,targetCode L]
    (addressTerm ctx ty k) xs ![ctx,ty,k] (addressGraph ctx ty k)
  intro j
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (Fin.cases off (fun e => Fin.elim0 e))) j

/-- Actual open acceptance of the guarded raw checker on a validated
fiber and a successful least produces the original scalar program at
that exact emitted target address. -/
theorem exact_OpenRawWithTargetReport (i cv tv : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty q w r k : OTerm α)
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (min : D B Γ (programGraph L (suc k) ![ctx,ty,r]))
    (step : D B Γ (programGraph (rawWithTarget i cv tv raw L) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r] ⊓ unary i (suc z) (addressTerm ctx ty k)) := by
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  obtain ⟨parts⟩ := conjunctionRecover raw (targetGate i cv tv L) xs step
  have valid := conjunctionAccept (atSlot cv 0) (atSlot tv 1) xs
    (slotCall cv 0 xs gc) (slotCall tv 1 xs gt)
  have guarded := successorBranchElim (addressGuards cv tv) (constantOne 5)
    (ID1Completion.InternalAcceptance.branch (targetLeast L) (constantOne 5) (targetScalar i L))
    (suc z) z xs valid ⟨Derivation.conjunctionRight parts⟩
  have present := packedLeastGraph L ctx ty q w r k min
  have inspected := successorBranchElim (targetLeast L) (constantOne 5) (targetScalar i L)
    (suc z) k xs present guarded
  have value := packedAddressGraph L ctx ty q w r k present
  have iok : D B Γ (unary i (suc z) (addressTerm ctx ty k)) := by
    apply compositionRecover i ![targetAddress L] (suc z) xs ![addressTerm ctx ty k] inspected
    intro a
    obtain rfl := Fin.eq_zero a
    exact value
  obtain ⟨openI⟩ := iok
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft parts) openI⟩

#print axioms exact_OpenRawWithTargetReport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierOpenProof
