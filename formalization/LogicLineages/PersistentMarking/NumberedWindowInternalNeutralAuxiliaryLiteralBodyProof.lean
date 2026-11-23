module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementObjectBranchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalRefinedPositiveProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalAtomicRefinement (atTarget refined)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)
open NumberedWindowInternalAuxBottomRefinementObjectChecks (exact_OpenAuxBottomForgets)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalAuxBottomMembershipObjectChecks (exact_AugmentedBottomMembership)
open NumberedWindowInternalRefinedPositiveProjectionProof (exact_OriginalRefinedPositiveProjection)
open NumberedWindowInternalNeutralAuxiliaryRefinement (neutralPositive)

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OrdinaryArithmetic.Term α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

/-- An explicit destination scalar check on every accepted neutral tape.
This is a separate arithmetic AST; equality to original numerics is
not claimed in this module. -/
def neutralWithCarrier (i : Program 1) (r : Program 3) : Program 3 :=
  conjunction (neutralPositive i r) (atTarget i)

/-- Put both already-proved bottom cases and the new free cone in one body.
The outer refinements retain their original leaf arrangements. -/
def literalNeutral (i : Program 1) (r : Program 3) : Data :=
  literalData i (augmented i (neutralWithCarrier i r))

attribute [local irreducible] programGraph

theorem exact_OpenLiteralNeutralCertificate (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x w y : OrdinaryArithmetic.Term α)
    (ok : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (certificate (literalNeutral i r) false c x y w))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (programGraph (neutralPositive i r) (suc z) ![x,w,y] ⊓ carrier (literalNeutral i r) false c y)) := by
  let R := augmented i (neutralWithCarrier i r)
  let S := literalNeutral i r
  let B := sourceBody S c
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![x,w,y]
  have held := (exact_CertificateRules i (jRaw i) R (dCore i R permutation)
    false c B α Γ x y w).1 ok
  rw [acceptsGraph] at held
  have outer := exact_OpenAuxBottomForgets i (refined i (neutralWithCarrier i r)) B α Γ x w y held
  have inner := exact_OriginalRefinedPositiveProjection i (neutralWithCarrier i r) xs outer
  obtain ⟨both⟩ := conjunctionRecover (neutralPositive i r) (atTarget i) xs inner
  have checked : Nonempty (Derivation B Γ (programGraph i (suc z) ![y])) := by
    have called := Derivation.conjunctionRight both
    unfold atTarget at called
    apply compositionRecover i (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) xs ![y] ⟨called⟩
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  have carried := (NumberedWindowInternalCoordinateChecks.exact_DomainRules i (jRaw i) R
    (dCore i R permutation) false c B α Γ y).2 checked
  obtain ⟨cy⟩ := carried
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft both) cy⟩

/-- Same-body uses of the genuine terminal continuations. There is no
membership transfer between two different ID1 definitions. -/
theorem exact_OpenLiteralNeutralBottomI (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x ctx ty : OrdinaryArithmetic.Term α)
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (equal x (packedBottomTerm ctx ty))))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (carrier (literalNeutral i r) false c x))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false x)) :=
  (exact_AugmentedBottomMembership.1 i (jRaw i) (neutralWithCarrier i r)
    (dCore i (augmented i (neutralWithCarrier i r)) permutation) c α Γ x ctx ty shape).1 held

theorem exact_OpenLiteralNeutralBottomAuxI (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x ctx dom cod stored arg : OrdinaryArithmetic.Term α)
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal x (packedAuxBottomTerm ctx dom cod stored arg))))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (carrier (literalNeutral i r) false c x))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false x)) :=
  (exact_AugmentedBottomMembership.2 i (jRaw i) (neutralWithCarrier i r)
    (dCore i (augmented i (neutralWithCarrier i r)) permutation) c α Γ x ctx dom cod stored arg shape).1 held

#print axioms exact_OpenLiteralNeutralCertificate
#print axioms exact_OpenLiteralNeutralBottomI
#print axioms exact_OpenLiteralNeutralBottomAuxI
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
