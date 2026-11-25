module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedPositiveRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedGuardedPushProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport witnessData)
open NumberedWindowInternalSparseAddressPositiveOpenBackwardProof (backward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (supply)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralPositiveEndpointGuardProof (positiveEndpointGuard)
open NumberedWindowInternalLiteralGuardedPositiveRowsProof (D exact_OpenGuardedPositiveEdge)

variable {α : Type} {Γ : List (Formula α)}

/-- Address the actually supplied positive fold and introduce its
certificate in the same guarded physical source body. -/
theorem exact_OpenGuardedPositiveFromFold (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y ctx ty p q cert : OTerm α) :
    let data := literalData i (positiveEndpointGuard i (addressPositive cv tv raw L))
    let B := sourceBody data c
    D B Γ (addressReport x ctx ty p) → D B Γ (addressReport y ctx ty q) →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) y) →
    D B Γ (programGraph (positive raw L) (suc z) ![ctx,ty,p,cert,q]) →
    D B Γ (edge data false c x y) := by
  intro data B first last gc gt si ti path
  obtain ⟨first⟩ := first
  obtain ⟨last⟩ := last
  obtain ⟨gc⟩ := gc
  obtain ⟨gt⟩ := gt
  obtain ⟨path⟩ := path
  have row : D B Γ (witnessData cv tv raw L x cert y ctx ty p q) :=
    ⟨Derivation.conjunctionIntroduction first (Derivation.conjunctionIntroduction last
      (Derivation.conjunctionIntroduction gc (Derivation.conjunctionIntroduction gt path)))⟩
  have packed := supply cv tv raw L x cert y ctx ty p q row
  exact exact_OpenGuardedPositiveEdge i cv tv raw L c x cert y (backward cv tv raw L x cert y packed) si ti

#print axioms exact_OpenGuardedPositiveFromFold
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedGuardedPushProof
