module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierObjectProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankZeroGuardIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalNeutralRankGuard (targetHasRank lowersRank rankApplication rankEven)
open NumberedWindowInternalNeutralRankGuardForgetsProof (exact_OpenRankApplicationForgets)
open NumberedWindowInternalRankUniversalCarrier
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume)

private theorem acceptsGraph {α : Type} (p : Program 3) (x w y : OTerm α) :
    accepts p x w y = programGraph p (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A true zero report makes the actual new application graph and the
original graph equivalent on the same open source/argument/output. -/
theorem exact_OpenRankZeroApplication (i g : Program 1) (p : Program 3) (f u y : OTerm α)
    (zero : Nonempty (Derivation B Γ (unary g z f))) :
    Nonempty (Derivation B Γ (accepts p f u y)) ↔
    Nonempty (Derivation B Γ (accepts (rankApplication i g p) f u y)) := by
  refine ⟨?_, exact_OpenRankApplicationForgets i g p f u y⟩
  intro h
  rw [acceptsGraph] at h ⊢
  exact zeroBranchIntro (atSource g) p (conjunction p (conjunction (targetHasRank g) (atTarget i)))
    (suc z) ![f,u,y] (callSlot g 0 z ![f,u,y] zero) h

/-- Restore the actual original positive witness in the complete
rank-guarded checker under genuine source zero and target scalar reports. -/
theorem exact_OpenRankZeroEvenTape (i g : Program 1) (r : Program 3) (x w y : OTerm α)
    (zero : Nonempty (Derivation B Γ (unary g z x)))
    (carrierY : Nonempty (Derivation B Γ (unary i (suc z) y)))
    (old : Nonempty (Derivation B Γ (accepts r x w y))) :
    Nonempty (Derivation B Γ (accepts (completeRankEven i g r) x w y)) := by
  rw [acceptsGraph] at old ⊢
  let base := alwaysCarried i r
  let checks := conjunction (targetHasRank g) (conjunction (atTarget i) (lowersRank g))
  let xs : Fin 3 → OTerm α := ![x,w,y]
  have call : Nonempty (Derivation B Γ (programGraph base (suc z) xs)) :=
    conjunctionAccept r (atTarget i) xs old (callSlot i 2 (suc z) xs carrierY)
  exact zeroBranchIntro (atSource g) base (conjunction base checks) (suc z) xs
    (callSlot g 0 z xs zero) call

/-- Same ambient proof, same actual old positive path and destination.
Only the explicitly mentioned source and target arithmetic reports are
needed to package it as an actual edge of the new selected body. -/
theorem exact_OpenRankZeroEvenEdge (i j g : Program 1) (r d : Program 3) (c : Nat) (x y : OTerm α)
    (zero : Nonempty (Derivation B Γ (unary g z x)))
    (carrierY : Nonempty (Derivation B Γ (unary i (suc z) y)))
    (old : Nonempty (Derivation B Γ (suppliedEdge r x y))) :
    Nonempty (Derivation B Γ (edge (data i j (completeRankEven i g r) d) false c x y)) := by
  apply consume r x y _ old
  intro β ρ Δ w keep tape
  rw [edgeRename]
  have z' := renameInto zero ρ Δ keep
  rw [unaryRename,zRelabel] at z'
  have i' := renameInto carrierY ρ Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at i'
  have next := exact_OpenRankZeroEvenTape i g r (x.relabel ρ) w (y.relabel ρ) z' i' tape
  exact edgeIntroduction ((exact_CertificateRules i j (completeRankEven i g r) d
    false c B β Δ (x.relabel ρ) (y.relabel ρ) w).2 next)

#print axioms exact_OpenRankZeroApplication
#print axioms exact_OpenRankZeroEvenTape
#print axioms exact_OpenRankZeroEvenEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRankZeroGuardIntroProof
