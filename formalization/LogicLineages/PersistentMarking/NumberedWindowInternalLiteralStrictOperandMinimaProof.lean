module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictClassRawSourceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalOriginalScalarAddressWindowProof (exact_OpenOriginalScalarAddressWindow)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralStrictClassRawSourceProof
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem changeType (L : Program 3) (ctx ty want q result : OTerm α)
    (eq : D B Γ (eqn ty want)) (h : D B Γ (programGraph L result ![ctx,ty,q])) :
    D B Γ (programGraph L result ![ctx,want,q]) := by
  unfold programGraph at *
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L) result ![ctx,ty,q] ![ctx,want,q] _ h
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx))
    (Fin.cases eq (Fin.cases (⟨refl q⟩ : D B Γ (eqn q q)) (fun n => Fin.elim0 n))) i

theorem exact_OpenStrictApplicationOperands (cv tv : Program 1) (W : Program 3)
    (core : Program 3) (finite : List Nat) (x u ctx result dom cod fn arg : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator core))
    let i := finiteScalar (addressScalar cv tv W L) finite
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (literalMembership finite (rawCons dom cod)) ∧
    D B Γ (literalMembership finite dom) ∧
    D B Γ (programGraph (childGuardedLeast core) (suc fn) ![ctx,rawCons dom cod,fn]) ∧
    D B Γ (programGraph (childGuardedLeast core) (suc arg) ![ctx,dom,arg]) := by
  intro L i left right parsed
  obtain ⟨all⟩ := parsed
  let uRows := Derivation.conjunctionRight all
  let arrowRows := Derivation.conjunctionRight uRows
  let fRows := Derivation.conjunctionRight arrowRows
  let aRows := Derivation.conjunctionRight fRows
  let coordinates := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight aRows))
  let arrowEq := Derivation.conjunctionLeft coordinates
  let fFields := Derivation.conjunctionLeft fRows
  let aFields := Derivation.conjunctionLeft aRows
  have fAddress : D B Γ (addressReport x ctx result fn) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft all) fFields⟩
  have aAddress : D B Γ (addressReport u ctx dom arg) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft uRows) aFields⟩
  have fType : D B Γ (unary rawResult result x) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fFields)⟩
  have aType : D B Γ (unary rawResult dom u) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight aFields)⟩
  have fTypeAt := ID1Completion.InternalControlGraphSupportProof.outputTransport rawResult result
    (rawCons dom cod) ![x] ⟨arrowEq⟩ fType
  obtain ⟨scx,fMemory⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) finite x
    (rawCons dom cod) fTypeAt left
  obtain ⟨scu,aMemory⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) finite u dom aType right
  obtain ⟨fnSelf⟩ := exact_OpenOriginalScalarAddressWindow cv tv W L x ctx result fn fAddress scx
  obtain ⟨argSelf⟩ := exact_OpenOriginalScalarAddressWindow cv tv W L u ctx dom arg aAddress scu
  have fAt := changeType L ctx result (rawCons dom cod) fn (suc fn) ⟨arrowEq⟩
    ⟨Derivation.conjunctionRight fnSelf⟩
  have fClass := exact_OpenStrictClassStackReport core ctx (rawCons dom cod) fn fn fAt
  have aClass := exact_OpenStrictClassStackReport core ctx dom arg arg ⟨Derivation.conjunctionRight argSelf⟩
  obtain ⟨fp⟩ := exact_OpenLiteralAuxClassLeastReport (childGuardedLeast core) ctx (rawCons dom cod) fn fn fClass
  obtain ⟨ap⟩ := exact_OpenLiteralAuxClassLeastReport (childGuardedLeast core) ctx dom arg arg aClass
  exact ⟨fMemory,aMemory,⟨Derivation.conjunctionLeft fp⟩,⟨Derivation.conjunctionLeft ap⟩⟩

/-- The actual accepted operand addresses are the selected minima that
the genuine contextual certificate sees. The source child comparison
is not supplied as a separate premise. -/
theorem exact_OpenStrictCertificateOperandMinima (cv tv : Program 1) (W : Program 3)
    (core : Program 3) (finite : List Nat) (x u ctx ty result dom cod fn arg q d e f a k : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator core))
    let i := finiteScalar (addressScalar cv tv W L) finite
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (programGraph L (suc k) ![ctx,ty,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc k) ![ctx,ty,q]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) →
    D B Γ (literalMembership finite (rawCons dom cod)) ∧ D B Γ (literalMembership finite dom) ∧
    D B Γ (eqn d dom) ∧ D B Γ (eqn e cod) ∧
    D B Γ (programGraph (childGuardedLeast core) (suc fn) ![ctx,rawCons d e,f]) ∧
    D B Γ (programGraph (childGuardedLeast core) (suc arg) ![ctx,d,a]) := by
  intro L i left right parsed seed source parts
  obtain ⟨fType,aType,fnReport,argReport⟩ := exact_OpenStrictApplicationOperands cv tv W core finite
    x u ctx result dom cod fn arg left right parsed
  obtain ⟨dEq,cEq,fnAt,argAt⟩ := exact_OpenStrictRawChildMinima core ctx ty dom cod fn arg q d e f a k fn arg
    seed source parts fnReport argReport
  exact ⟨fType,aType,dEq,cEq,fnAt,argAt⟩

#print axioms exact_OpenStrictApplicationOperands
#print axioms exact_OpenStrictCertificateOperandMinima
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
