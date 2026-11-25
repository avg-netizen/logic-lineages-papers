module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedApplicationFormationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationInputCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationCoverageWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationFormationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralDecoratedApplicationFormationProof (OpenAuxFormation)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenCoverageFromLeastOn)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalAuxWindowStepTargets (windowUpdate intrinsicQuery TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowThinOpenChecks (exact_OpenAuxWindow)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteCodes finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralFiniteCodomainProof
  (exact_OpenLiteralFiniteCodomain exact_OpenLiteralFiniteTypeTests)
open NumberedWindowInternalLiteralApplicationInputCoordinatesProof (exact_OpenLiteralApplicationInputCoordinates)

open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (OpenDecorator)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

open NumberedWindowInternalLiteralApplicationCoverageWindowProof
  (coveredFormationWindow exact_OpenCoveredFormationWindow)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)

/-- Both scalar inputs retain physical finite type reports. The same
installed forming window and the same type guards then give a formed
auxiliary at its actual codomain. No claim is made that this window
is definitionally interchangeable with a different memo program. -/
theorem exact_OpenEnrichedApplicationFormation (s : Settings) (P : List ProbeTy)
    (closed : ChildClosed P) (cv tv T : Program 1) (C W : Program 3) (E : Program 4) (forms : OpenAuxFormation C s W T)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (f u ctx r dom cod fn arg k : OTerm α) :
    let L := guardedLeast (headerLeast (decorate (packedLeastOn C E s)))
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg) →
    D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) cod) ∧
    D B Γ (literalMembership (finiteCodes P) cod) ∧
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg)) := by
  intro L i left right parsed selected
  obtain ⟨p⟩ := parsed
  let uFields := Derivation.conjunctionRight p
  let arrowFields := Derivation.conjunctionRight uFields
  let leftFields := Derivation.conjunctionRight arrowFields
  let rightFields := Derivation.conjunctionRight leftFields
  let arrows := Derivation.conjunctionRight rightFields
  let equalities := Derivation.conjunctionRight arrows
  let resultEq := Derivation.conjunctionLeft (Derivation.conjunctionRight equalities)
  have source : D B Γ (unary rawResult r f) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionLeft leftFields))⟩
  have domain : D B Γ (unary rawResult dom u) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionLeft rightFields))⟩
  have arrowReport : D B Γ (unary rawResult (rawCons dom cod) f) :=
    outputTransport rawResult r (rawCons dom cod) ![f] ⟨resultEq⟩ source
  obtain ⟨s₁,finiteArrow⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) (finiteCodes P)
    f (rawCons dom cod) arrowReport left
  obtain ⟨s₂,finiteDom⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) (finiteCodes P)
    u dom domain right
  have finiteCod := exact_OpenLiteralFiniteCodomain P closed dom cod finiteArrow
  have domT := (exact_OpenLiteralFiniteTypeTests s P tv T tvFit TFit included dom finiteDom).2
  obtain ⟨codTV,codT⟩ := exact_OpenLiteralFiniteTypeTests s P tv T tvFit TFit included cod finiteCod
  obtain ⟨gc,_,_,wf,wu⟩ := exact_OpenLiteralApplicationInputCoordinates cv tv W L
    f u ctx r dom cod fn arg s₁ s₂ ⟨p⟩
  let seed := auxiliaryTerm dom cod fn arg
  let L₀ := decorate (packedLeastOn C E s)
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast L₀) ctx cod seed k selected
  obtain ⟨head⟩ := exact_OpenLiteralHeaderLeastReport L₀ ctx cod seed k
    ⟨Derivation.conjunctionLeft atom⟩
  have actual : D B Γ (leastOnGraph C E s ctx cod seed k) :=
    bridge.erase (packedLeastOn C E s) B α Γ ctx cod seed k ⟨Derivation.conjunctionLeft head⟩
  have cover := exact_OpenCoverageFromLeastOn C E s ctx cod seed k actual
  exact ⟨gc,codTV,finiteCod,forms B α Γ ctx dom cod fn arg domT codT wf wu cover⟩


#print axioms exact_OpenEnrichedApplicationFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationFormationProof
