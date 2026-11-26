module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralStrictForkRetapeProof (exact_OpenStrictArrowRetape)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof (exact_OpenLiteralAuxProfileLeastReport)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast fullAuxiliaryDecorator)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenStrictApplicationTermRetape (r d c f a d' c' a' : OTerm α)
    (atRaw : D B Γ (eqn r (auxiliaryTerm d' c' f a')))
    (dom : D B Γ (eqn d d')) (cod : D B Γ (eqn c c')) (arg : D B Γ (eqn a a')) :
    D B Γ (eqn r (auxiliaryTerm d c f a)) := by
  -- The original nested cells have the same numeric tag and unchanged function slot.
  have endArgs := exact_OpenStrictArrowRetape a z a' z arg ⟨refl z⟩
  have terms := exact_OpenStrictArrowRetape f (rawCons a z) f (rawCons a' z) ⟨refl f⟩ endArgs
  have codoms := exact_OpenStrictArrowRetape c (rawCons f (rawCons a z))
    c' (rawCons f (rawCons a' z)) cod terms
  have doms := exact_OpenStrictArrowRetape d (rawCons c (rawCons f (rawCons a z)))
    d' (rawCons c' (rawCons f (rawCons a' z))) dom codoms
  have heads := exact_OpenStrictArrowRetape (numeral 6) _ (numeral 6) _ ⟨refl _⟩ doms
  obtain ⟨found⟩ := atRaw
  obtain ⟨aligned⟩ := heads
  exact ⟨trans found (symm aligned)⟩

theorem exact_OpenStrictRetapeTypeAndRaw (L : Program 3) (ctx ty ty' q q' value : OTerm α)
    (type : D B Γ (eqn ty ty')) (raw : D B Γ (eqn q q'))
    (held : D B Γ (programGraph L value ![ctx,ty,q])) :
    D B Γ (programGraph L value ![ctx,ty',q']) := by
  unfold programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L)
    value ![ctx,ty,q] ![ctx,ty',q'] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx))
    (Fin.cases type (Fin.cases raw (fun e => Fin.elim0 e))) i

theorem exact_OpenStrictChildPrimitiveReport (L : Program 3) (ctx ty q k : OTerm α)
    (held : D B Γ (programGraph (childGuardedLeast L) (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc k) ![ctx,ty,q]) := by
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (auxProfileLeast L)) ctx ty q k held
  obtain ⟨head⟩ := exact_OpenLiteralHeaderLeastReport (auxProfileLeast L) ctx ty q k
    ⟨Derivation.conjunctionLeft atom⟩
  obtain ⟨profile⟩ := exact_OpenLiteralAuxProfileLeastReport L ctx ty q k ⟨Derivation.conjunctionLeft head⟩
  exact ⟨Derivation.conjunctionLeft profile⟩

theorem exact_OpenStrictFullPrimitiveReport (L : Program 3) (ctx ty q k : OTerm α)
    (held : D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator L))) (suc k)
      ![ctx,ty,q])) :
    D B Γ (programGraph L (suc k) ![ctx,ty,q]) := by
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (fullAuxiliaryDecorator L)) ctx ty q k held
  obtain ⟨head⟩ := exact_OpenLiteralHeaderLeastReport (fullAuxiliaryDecorator L) ctx ty q k
    ⟨Derivation.conjunctionLeft atom⟩
  obtain ⟨classes⟩ := exact_OpenLiteralAuxClassLeastReport (childGuardedLeast L) ctx ty q k
    ⟨Derivation.conjunctionLeft head⟩
  exact exact_OpenStrictChildPrimitiveReport L ctx ty q k ⟨Derivation.conjunctionLeft classes⟩

/-- Keep the original auxiliary argument address and its actual class
coordinate while retaping the already checked equal lexical/type fields. -/
theorem exact_OpenStrictOriginalArgumentAddress (x u ctx result dom cod fn arg sc d : OTerm α)
    (normal : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg))
    (sameCtx : D B Γ (eqn ctx sc)) (sameTy : D B Γ (eqn dom d)) :
    D B Γ (addressReport u sc d arg) := by
  obtain ⟨whole⟩ := normal
  let uRows := Derivation.conjunctionRight whole
  let arrowRows := Derivation.conjunctionRight uRows
  let fRows := Derivation.conjunctionRight arrowRows
  let aRows := Derivation.conjunctionRight fRows
  let fields := Derivation.conjunctionLeft aRows
  obtain ⟨scope⟩ := outputTransport rawContext ctx sc ![u] sameCtx ⟨Derivation.conjunctionLeft fields⟩
  obtain ⟨ty⟩ := outputTransport rawResult dom d ![u] sameTy
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fields)⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft uRows)
    (Derivation.conjunctionIntroduction scope
      (Derivation.conjunctionIntroduction ty (Derivation.conjunctionRight (Derivation.conjunctionRight fields))))⟩

#print axioms exact_OpenStrictApplicationTermRetape
#print axioms exact_OpenStrictRetapeTypeAndRaw
#print axioms exact_OpenStrictChildPrimitiveReport
#print axioms exact_OpenStrictFullPrimitiveReport
#print axioms exact_OpenStrictOriginalArgumentAddress
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
