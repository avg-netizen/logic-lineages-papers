module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredCarrierInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCarrierChildHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph)
open NumberedWindowInternalLiteralHopCarrier
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildHopProof (exact_OpenOneHopFromLeastTapes)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop directFromOne)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftValidator (p : Program 1) (k : Fin 5) (xs : Fin 5 → OTerm α)
    (h : D B Γ (unary p (suc z) (xs k))) :
    D B Γ (programGraph (atSlot p k) (suc z) xs) := by
  apply compositionValue p ![.projection k] (suc z) xs ![xs k] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue k xs

/-- On the actual validated input and exact resulting least report,
an already available scalar graph at the destination is sufficient
to reassemble the very same current wrapped raw step. -/
theorem exact_OpenRawWithTargetIntro (i cv tv : Program 1) (R : Program 5) (L : Program 3)
    (ctx ty q w r k : OTerm α)
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (mn : D B Γ (programGraph L (suc k) ![ctx,ty,r]))
    (hit : D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r]))
    (sat : D B Γ (unary i (suc z) (addressTerm ctx ty k))) :
    D B Γ (programGraph (rawWithTarget i cv tv R L) (suc z) ![ctx,ty,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  have min : D B Γ (programGraph (targetLeast L) (suc k) xs) := by
    apply compositionValue L ![.projection 0,.projection 1,.projection 4] (suc k) xs ![ctx,ty,r] mn
    intro j
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 4 xs) (fun e => Fin.elim0 e))) j
  have pred : D B Γ (unary predOne k (suc k)) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor k
  have code : D B Γ (programGraph (targetCode L) k xs) := by
    apply compositionValue predOne ![targetLeast L] k xs ![suc k] pred
    intro j
    obtain rfl := Fin.eq_zero j
    exact min
  have addr : D B Γ (programGraph (targetAddress L) (addressTerm ctx ty k) xs) := by
    apply compositionValue addressEmitter ![.projection 0,.projection 1,targetCode L]
      (addressTerm ctx ty k) xs ![ctx,ty,k] (addressGraph ctx ty k)
    intro j
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases code (fun e => Fin.elim0 e))) j
  have scalar : D B Γ (programGraph (targetScalar i L) (suc z) xs) := by
    apply compositionValue i ![targetAddress L] (suc z) xs ![addressTerm ctx ty k] sat
    intro j
    obtain rfl := Fin.eq_zero j
    exact addr
  have valid := conjunctionAccept (atSlot cv 0) (atSlot tv 1) xs
    (liftValidator cv 0 xs gc) (liftValidator tv 1 xs gt)
  have leastBranch := successorBranchIntro (targetLeast L) (constantOne 5) (targetScalar i L) (suc z) k xs min scalar
  have inside := successorBranchIntro (addressGuards cv tv) (constantOne 5)
    (ID1Completion.InternalAcceptance.branch (targetLeast L) (constantOne 5) (targetScalar i L)) (suc z) z xs valid leastBranch
  exact conjunctionAccept R (targetGate i cv tv L) xs hit inside

/-- The underlying child need not be run again with surplus fuel or a
changed argument. At the actual two least outputs, the remaining
scalar graph gives its direct edge in the same wrapped parent body. -/
theorem exact_OpenCarrierChildHopAtLeast (i cv tv : Program 1) (R : Program 5) (L : Program 3)
    (c : Nat) (ctx ty q w r a b : OTerm α) :
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r]) →
    D B Γ (programGraph L (suc a) ![ctx,ty,q]) →
    D B Γ (programGraph L (suc b) ![ctx,ty,r]) →
    D B Γ (unary i (suc z) (literalAddress ctx ty b)) →
    D B Γ (direct data (hop cv tv raw L) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  intro raw data B gc gt held left right sat
  obtain ⟨rawStep⟩ := exact_OpenRawWithTargetIntro i cv tv R L ctx ty q w r b gc gt right held sat
  obtain ⟨sourceMin⟩ := left
  obtain ⟨dest⟩ := right
  have one := exact_OpenOneHopFromLeastTapes cv tv raw L ctx ty a b q w r gc gt
    ⟨Derivation.conjunctionIntroduction rawStep (Derivation.conjunctionIntroduction sourceMin dest)⟩
  exact directFromOne i cv tv raw L c ctx ty a b q w r one

#print axioms exact_OpenRawWithTargetIntro
#print axioms exact_OpenCarrierChildHopAtLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCarrierChildHopProof
