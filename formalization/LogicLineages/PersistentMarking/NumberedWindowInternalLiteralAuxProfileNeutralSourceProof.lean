module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxHeaderTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileNeutralSourceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead cellGood)
open NumberedWindowInternalSparseRawFunctionFrame (termShape frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports onTape)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D rejectZeroOutput)
open NumberedWindowInternalLiteralAuxProfileLeastProof (functionHead auxProfileLeast matchCoordinates)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof
  (exact_OpenLiteralAuxProfileShape exact_OpenLiteralAuxProfileFields exact_OpenLiteralAuxCoordinateTransfer)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource notLambdaHeader rawHeader)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast addressGood)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev lambdaAt {α : Type} (h : OTerm α) : Formula α :=
  programGraph equalityTest z ![h,numeral 2]

/-- The actual neutral-address test exposes zero of the original
numeric lambda-header comparison at the actual raw function. -/
theorem exact_OpenNeutralHeaderNotLambda (x fn h : OTerm α)
    (known : D B Γ (atom neutralSource x)) (fieldValue : D B Γ (unary rawLeast fn x))
    (head : D B Γ (unary cellHead h fn)) :
    D B Γ (lambdaAt h) := by
  let test := NumberedWindowInternalLiteralNeutralAtomProof.lambdaHeader
  obtain ⟨pair⟩ := conjunctionRecover addressGood notLambdaHeader ![x] known
  have passed : D B Γ (unary notLambdaHeader (suc z) x) := ⟨Derivation.conjunctionRight pair⟩
  have testZero : D B Γ (unary test z x) := by
    apply NumberedWindowInternalFreshProbeProof.optionGraphCases test ![x] _
    · intro β j Δ keep absent
      simp only [unary,programRename,inputsRename,zRelabel]
      simpa only [inputsRename] using absent
    · intro β j Δ pred keep typed
      simp only [inputsRename] at typed
      simp only [unary,programRename,inputsRename,zRelabel]
      have moved := renameInto passed j Δ keep
      simp only [unary,programRename,inputsRename,sucRelabel,zRelabel] at moved
      let xs : Fin 1 → OTerm β := ![x.relabel j]
      have bad := successorBranchElim test (literal 1 1) (constantZero 1) (suc z) pred
        xs typed moved
      obtain ⟨eq⟩ := valueUnique (constantZero 1) (suc z) z xs bad (constantZeroValue xs)
      exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  have read := makeUnary cellHead rawLeast h x fn head fieldValue
  apply compositionRecover equalityTest ![rawHeader,literal 1 2] z ![x] ![h,numeral 2] testZero
  exact fun i => Fin.cases read (Fin.cases (literalGraph 2 ![x]) (fun e => Fin.elim0 e)) i

private theorem rawReject (fn h : OTerm α) (head : D B Γ (unary cellHead h fn))
    (held : D B Γ (lambdaAt h)) :
    D B Γ (unary NumberedWindowInternalLiteralAuxRootLeaf.lambdaHeader z fn) := by
  let c : Program 1 := .composition equalityTest ![cellHead,literal 1 2]
  have rejected : D B Γ (unary c z fn) := by
    apply compositionValue equalityTest ![cellHead,literal 1 2] z ![fn] ![h,numeral 2] held
    exact fun i => Fin.cases head (Fin.cases (literalGraph 2 ![fn]) (fun e => Fin.elim0 e)) i
  let fact := programGraph (conjunction cellGood c) (suc z) ![fn]
  have no : D B Γ fact.not := by
    obtain ⟨rz⟩ := rejected
    have now : D B (fact :: Γ) fact := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨parts⟩ := conjunctionRecover cellGood c ![fn] now
    obtain ⟨bad⟩ := valueUnique c (suc z) z ![fn] ⟨Derivation.conjunctionRight parts⟩ ⟨addHyp rz _⟩
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩
  exact conjunctionReject cellGood c ![fn] no

private theorem functionReject (q w r h : OTerm α)
    (accepted : D B Γ (unary functionHead h q)) (nonlambda : D B Γ (lambdaAt h)) :
    D B Γ (programGraph functionLambdaHeader z ![q,w,r]) := by
  apply programCases (field 2) ![q] _
  intro β j Δ fn keep picked
  rw [inputsRename] at picked
  simp only [programRename,tripleInputsRename,zRelabel]
  have active := renameInto accepted j Δ keep
  simp only [unary,programRename,inputsRename] at active
  have no := renameInto nonlambda j Δ keep
  rw [lambdaAt,programRename,zRelabel] at no
  have pair : (fun i : Fin 2 => ((![h,numeral 2] : Fin 2 → OTerm α) i).relabel j) =
      ![h.relabel j,numeral 2] := by
    funext i
    refine Fin.cases rfl (Fin.cases ?_ (fun e => Fin.elim0 e)) i
    exact numeralRename 2 j
  rw [pair] at no
  have head : D B Δ (unary cellHead (h.relabel j) fn) := by
    apply compositionRecover cellHead (Fin.cons (field 2) Fin.elim0) (h.relabel j)
      ![q.relabel j] ![fn] active
    intro k
    obtain rfl := Fin.eq_zero k
    exact picked
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  apply compositionValue NumberedWindowInternalLiteralAuxRootLeaf.lambdaHeader ![frameSlot 2 0]
    z xs ![fn] (rawReject fn (h.relabel j) head no)
  intro k
  obtain rfl := Fin.eq_zero k
  exact onTape (field 2) 0 fn xs picked

/-- Two genuine queries that return the same representative transport
the literal application seed's auxiliary shape and non-lambda
function header to the raw source of a direct certificate. -/
theorem exact_OpenAuxiliarySourceFromSharedProfile (L : Program 3)
    (ctx ty dom cod fn arg q w r selected h : OTerm α)
    (left : D B Γ (programGraph (auxProfileLeast L) (suc selected)
      ![ctx,ty,auxiliaryTerm dom cod fn arg]))
    (right : D B Γ (programGraph (auxProfileLeast L) (suc selected) ![ctx,ty,q]))
    (head : D B Γ (unary cellHead h fn)) (nonlambda : D B Γ (lambdaAt h)) :
    D B Γ (programGraph sourceIsAux (suc z) ![q,w,r] ⊓ programGraph functionLambdaHeader z ![q,w,r]) := by
  let seed := auxiliaryTerm dom cod fn arg
  obtain ⟨literalAux,fields⟩ := termReports (body := B) (Γ := Γ) dom cod fn arg
  have computed : D B Γ (unary functionHead h seed) := by
    apply compositionValue cellHead (Fin.cons (field 2) Fin.elim0) h ![seed] ![fn] head
    intro i
    obtain rfl := Fin.eq_zero i
    exact fields.2.2.1
  have selectedShape := (exact_OpenLiteralAuxProfileShape L ctx ty seed selected left).1 literalAux
  have sourceShape := (exact_OpenLiteralAuxProfileShape L ctx ty q selected right).2 selectedShape
  obtain ⟨first⟩ := exact_OpenLiteralAuxProfileFields L ctx ty seed selected left literalAux
  obtain ⟨second⟩ := exact_OpenLiteralAuxProfileFields L ctx ty q selected right sourceShape
  have chosenHead := (exact_OpenLiteralAuxCoordinateTransfer functionHead seed selected h
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight first)⟩).1 computed
  have sourceHead := (exact_OpenLiteralAuxCoordinateTransfer functionHead q selected h
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight second)⟩).2 chosenHead
  obtain ⟨known⟩ := onTape termShape 0 (suc z) ![q,w,r] sourceShape
  obtain ⟨notL⟩ := functionReject q w r h sourceHead nonlambda
  exact ⟨Derivation.conjunctionIntroduction known notL⟩

#print axioms exact_OpenNeutralHeaderNotLambda
#print axioms exact_OpenAuxiliarySourceFromSharedProfile
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileNeutralSourceProof
