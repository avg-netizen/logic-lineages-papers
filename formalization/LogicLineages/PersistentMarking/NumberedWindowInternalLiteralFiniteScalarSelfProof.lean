module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarSelfProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The exact finite scalar has both the original window and same
physical successful self least on the reported address; it also
retains the actual finite type witness. -/
theorem exact_OpenLiteralFiniteScalarSelf (cv tv : Program 1) (W L : Program 3) (codes : List Nat)
    (q ctx ty raw : OTerm α)
    (shell : D B Γ (addressReport q ctx ty raw))
    (held : D B Γ (unary (finiteScalar (addressScalar cv tv W L) codes) (suc z) q)) :
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) ty) ∧
    D B Γ (windowAt W ctx ty raw) ∧ D B Γ (programGraph L (suc raw) ![ctx,ty,raw]) ∧
    D B Γ (literalMembership codes ty) := by
  obtain ⟨shape⟩ := shell
  have result : D B Γ (unary rawResult ty q) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight shape))⟩
  obtain ⟨⟨scalar⟩,listed⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) codes q ty result held
  obtain ⟨f⟩ := reported cv tv W L B α Γ q ctx ty raw
  let paid := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination f shape)) scalar
  obtain ⟨g⟩ := openTest W L B α Γ ctx ty raw
  let checked := Derivation.implicationElimination (Derivation.conjunctionLeft g)
    (Derivation.conjunctionRight (Derivation.conjunctionRight paid))
  exact ⟨⟨Derivation.conjunctionLeft paid⟩,
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight paid)⟩,
    ⟨Derivation.conjunctionLeft checked⟩,⟨Derivation.conjunctionRight checked⟩,listed⟩

#print axioms exact_OpenLiteralFiniteScalarSelf
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarSelfProof
