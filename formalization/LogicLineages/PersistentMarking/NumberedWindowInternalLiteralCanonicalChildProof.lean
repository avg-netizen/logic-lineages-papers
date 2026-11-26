module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCarrierChildHopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress exact_OriginalLiteralAddressReport)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralCarrierChildHopProof (exact_OpenCarrierChildHopAtLeast)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The scalar callback at an exact literal address uses no hypothetical
predicate. The two original validators plus actual window membership
and a real self-least report suffice for the physical scalar graph. -/
theorem exact_OpenLiteralScalarFromSelfLeast (cv tv : Program 1) (W L : Program 3)
    (ctx ty k : OTerm α) (gc : D B Γ (unary cv (suc z) ctx))
    (gt : D B Γ (unary tv (suc z) ty)) (valid : D B Γ (windowAt W ctx ty k))
    (self : D B Γ (programGraph L (suc k) ![ctx,ty,k])) :
    D B Γ (unary (addressScalar cv tv W L) (suc z) (literalAddress ctx ty k)) := by
  obtain ⟨toCoordinates⟩ := NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof.openTest
    W L B α Γ ctx ty k
  obtain ⟨toAddress⟩ := NumberedWindowInternalSparseCanonicalAddressFieldsThinProof.reported
    cv tv W L B α Γ (literalAddress ctx ty k) ctx ty k
  obtain ⟨context⟩ := gc
  obtain ⟨resultType⟩ := gt
  obtain ⟨inWindow⟩ := valid
  obtain ⟨minimum⟩ := self
  obtain ⟨report⟩ := exact_OriginalLiteralAddressReport (B := B) (Γ := Γ) ctx ty k
  have coords := Derivation.implicationElimination (Derivation.conjunctionRight toCoordinates)
    (Derivation.conjunctionIntroduction inWindow minimum)
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination toAddress report))
    (Derivation.conjunctionIntroduction context (Derivation.conjunctionIntroduction resultType coords))⟩

/-- At a canonical computed child destination, the actual wrapped
direct check is reconstructed from the original raw step and the two
exact least reports. The missing premises are visible derivations of
window membership at the selected code and least idempotence there. -/
theorem exact_OpenCanonicalChildHopAtLeast (cv tv : Program 1) (W L : Program 3) (R : Program 5)
    (c : Nat) (ctx ty q w r a b : OTerm α) :
    let i := addressScalar cv tv W L
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r]) →
    D B Γ (programGraph L (suc a) ![ctx,ty,q]) →
    D B Γ (programGraph L (suc b) ![ctx,ty,r]) →
    D B Γ (windowAt W ctx ty b) →
    D B Γ (programGraph L (suc b) ![ctx,ty,b]) →
    D B Γ (direct data (hop cv tv raw L) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  intro i raw data B gc gt held left right valid self
  exact exact_OpenCarrierChildHopAtLeast i cv tv R L c ctx ty q w r a b gc gt held left right
    (exact_OpenLiteralScalarFromSelfLeast cv tv W L ctx ty b gc gt valid self)

#print axioms exact_OpenLiteralScalarFromSelfLeast
#print axioms exact_OpenCanonicalChildHopAtLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
