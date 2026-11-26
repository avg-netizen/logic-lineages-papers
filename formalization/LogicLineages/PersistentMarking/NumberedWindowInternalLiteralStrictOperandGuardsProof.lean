module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandGuardsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The function's admitted finite scalar already pays the exact original
lexical and arrow-type gates. They are recovered from the same parsed
operand report used by the accepted application, rather than supplied as
new premises to the nested child step. -/
theorem exact_OpenStrictFunctionOperandGuards (cv tv : Program 1) (W L : Program 3) (finite : List Nat)
    (x u ctx result dom cod fn arg : OTerm α)
    (left : D B Γ (unary (finiteScalar (addressScalar cv tv W L) finite) (suc z) x))
    (parsed : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg)) :
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) (rawCons dom cod)) ∧
      D B Γ (literalMembership finite (rawCons dom cod)) := by
  obtain ⟨all⟩ := parsed
  let uRows := Derivation.conjunctionRight all
  let arrowRows := Derivation.conjunctionRight uRows
  let fRows := Derivation.conjunctionRight arrowRows
  let aRows := Derivation.conjunctionRight fRows
  let cords := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight aRows))
  let arrowEq := Derivation.conjunctionLeft cords
  let fFields := Derivation.conjunctionLeft fRows
  let addr : Derivation B Γ (addressReport x ctx result fn) :=
    Derivation.conjunctionIntroduction (Derivation.conjunctionLeft all) fFields
  have read : D B Γ (unary rawResult result x) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fFields)⟩
  have expected := outputTransport rawResult result (rawCons dom cod) ![x] ⟨arrowEq⟩ read
  obtain ⟨scalar,mem⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) finite x
    (rawCons dom cod) expected left
  obtain ⟨openAddress⟩ := reported cv tv W L B α Γ x ctx result fn
  have both := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination openAddress addr)) (Classical.choice scalar)
  exact ⟨⟨Derivation.conjunctionLeft both⟩,
    headTransport tv (suc z) result (rawCons dom cod) ![] ⟨arrowEq⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight both)⟩,mem⟩

#print axioms exact_OpenStrictFunctionOperandGuards
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandGuardsProof
