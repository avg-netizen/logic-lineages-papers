module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarSelfProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedCertifiedCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInversionSourceWitnessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralFiniteScalarSelfProof (exact_OpenLiteralFiniteScalarSelf)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (auxiliaryDecorator)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast)
open NumberedWindowInternalLiteralAuxClassRawSourceProof (exact_OpenAuxRawChildMinima)
open NumberedWindowInternalLiteralDecoratedCertifiedCasesProof (exact_OpenDecoratedAuxProfileFromStack)

open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onFiber (L : Program 3) (ctx sc ty st raw out : OTerm α)
    (c : D B Γ (eqn ctx sc)) (t : D B Γ (eqn ty st))
    (call : D B Γ (programGraph L out ![ctx,ty,raw])) :
    D B Γ (programGraph L out ![sc,st,raw]) := by
  unfold programGraph at call ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L)
    out ![ctx,ty,raw] ![sc,st,raw] _ call
  intro j
  rw [onEquality]
  exact Fin.cases c (Fin.cases t
    (Fin.cases (⟨refl raw⟩ : D B Γ (eqn raw raw)) (fun v => Fin.elim0 v))) j

private theorem consEqual (x y u v : OTerm α)
    (first : Nonempty (Derivation B Γ (eqn x u)))
    (second : Nonempty (Derivation B Γ (eqn y v))) :
    Nonempty (Derivation B Γ (eqn (rawCons x y) (rawCons u v))) := by
  let before : Fin 2 → OTerm α := ![x,y]
  let after : Fin 2 → OTerm α := ![u,v]
  have input (i : Fin 2) :
      Nonempty (Derivation B Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases first (Fin.cases second (fun n => Fin.elim0 n)) i
  have old : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) before)) :=
    consGraph x y
  unfold programGraph at old
  have moved : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) after)) := by
    unfold programGraph
    exact graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (rawCons x y) before after input old
  exact valueUnique fieldCons (rawCons x y) (rawCons u v) after moved (consGraph u v)


/-- In an actual contextual certificate branch, the original finite
scalar checks give genuine self minima of the two operands. The
chosen decorator transports those exact class codes to the raw child
at the certificate source's genuine type and context. It does not
construct a new child direct edge or any destination scalar. -/
theorem exact_OpenLiteralInversionSourceWitness
    (cv tv : Program 1) (W L₀ : Program 3) (codes : List Nat)
    (x u ctx result dom cod fn arg sc st before q d e f a : OTerm α) :
    let L := guardedLeast (headerLeast (auxiliaryDecorator L₀))
    let i := finiteScalar (addressScalar cv tv W L) codes
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (eqn sc ctx) →
    D B Γ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc before) ![sc,st,q]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) →
    D B Γ (unary cv (suc z) sc) ∧ D B Γ (unary tv (suc z) (rawCons d e)) ∧
    D B Γ (eqn d dom) ∧ D B Γ (eqn e cod) ∧
    D B Γ (programGraph (auxProfileLeast L₀) (suc fn) ![sc,rawCons d e,f]) ∧
    D B Γ (programGraph (auxProfileLeast L₀) (suc arg) ![sc,d,a]) := by
  intro L i one two input c app step shape
  obtain ⟨report⟩ := input
  let uFields := Derivation.conjunctionRight report
  let arrowFields := Derivation.conjunctionRight uFields
  let px := Derivation.conjunctionRight arrowFields
  let pu := Derivation.conjunctionRight px
  let resultEq := Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight pu)))
  have left : D B Γ (addressReport x ctx result fn) := ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft report) (Derivation.conjunctionLeft px)⟩
  have right : D B Γ (addressReport u ctx dom arg) := ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft uFields) (Derivation.conjunctionLeft pu)⟩
  obtain ⟨gc,gt,_,sf,_⟩ := exact_OpenLiteralFiniteScalarSelf cv tv W L codes x ctx result fn left one
  obtain ⟨_,_,_,su,_⟩ := exact_OpenLiteralFiniteScalarSelf cv tv W L codes u ctx dom arg right two
  obtain ⟨cell⟩ := c
  have g₀ := headTransport cv (suc z) ctx sc ![] ⟨symm cell⟩ gc
  have fnSelf := onFiber L ctx sc result (rawCons dom cod) fn (suc fn) ⟨symm cell⟩ ⟨resultEq⟩ sf
  have argSelf := onFiber L ctx sc dom dom arg (suc arg) ⟨symm cell⟩ ⟨refl dom⟩ su
  have bF := exact_OpenDecoratedAuxProfileFromStack L₀ sc (rawCons dom cod) fn fn fnSelf
  have bA := exact_OpenDecoratedAuxProfileFromStack L₀ sc dom arg arg argSelf
  obtain ⟨ed,ec,comparF,comparA⟩ := exact_OpenAuxRawChildMinima L₀ sc st dom cod fn arg
    q d e f a before fn arg app step shape bF bA
  have originalType := headTransport tv (suc z) result (rawCons dom cod) ![] ⟨resultEq⟩ gt
  have arrowEq : D B Γ (eqn (rawCons d e) (rawCons dom cod)) :=
    consEqual d e dom cod ed ec
  obtain ⟨same⟩ := arrowEq
  exact ⟨g₀,headTransport tv (suc z) (rawCons dom cod) (rawCons d e) ![] ⟨symm same⟩ originalType,
    ed,ec,comparF,comparA⟩

#print axioms exact_OpenLiteralInversionSourceWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInversionSourceWitnessProof
