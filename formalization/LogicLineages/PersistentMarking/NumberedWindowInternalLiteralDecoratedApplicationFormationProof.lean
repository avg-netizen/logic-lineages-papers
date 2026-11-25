module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationInputCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationCoverageWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedApplicationFormationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
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
open NumberedWindowInternalLiteralLeastCoverageProof (exact_OpenCoverageFromLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)

/-- The actual window's only formation interface: using its own
children, typed guards and reported literal coverage, build the
parent. This is a rule about derivations, not a numeric equivalence. -/
def OpenAuxFormation (C : Program 3) (s : Settings) (W : Program 3) (T : Program 1) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    D B Γ (unary T (suc z) dom) → D B Γ (unary T (suc z) cod) →
    D B Γ (windowAt W ctx (rawCons dom cod) fn) → D B Γ (windowAt W ctx dom arg) →
    D B Γ (coverageReport C s ctx (auxiliaryTerm dom cod fn arg)) →
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg))

theorem exact_OpenSimpleCoveredFormation (C : Program 3) (s : Settings) (base : Program 2) (T : Program 1) :
    OpenAuxFormation C s (coveredFormationWindow C s base T) T := by
  intro B α Γ ctx dom cod fn arg domT codT wf wu cover
  obtain ⟨rule⟩ := exact_OpenAuxWindow base T B α Γ ctx dom cod fn arg
  obtain ⟨d⟩ := domT
  obtain ⟨c⟩ := codT
  let seed := auxiliaryTerm dom cod fn arg
  obtain ⟨fw⟩ := (exact_OpenCoveredFormationWindow C s base T ctx (rawCons dom cod) fn).1 wf |>.1
  obtain ⟨aw⟩ := (exact_OpenCoveredFormationWindow C s base T ctx dom arg).1 wu |>.1
  have simple := Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction d c)
      (Derivation.conjunctionIntroduction fw aw))
  exact (exact_OpenCoveredFormationWindow C s base T ctx cod seed).2 ⟨simple⟩ cover

/-- Both scalar inputs retain physical finite type reports. The same
installed forming window and the same type guards then give a formed
auxiliary at its actual codomain. No claim is made that this window
is definitionally interchangeable with a different memo program. -/
theorem exact_OpenDecoratedApplicationFormationWith (s : Settings) (P : List ProbeTy)
    (closed : ChildClosed P) (cv tv T : Program 1) (C W : Program 3) (X : Program 2) (forms : OpenAuxFormation C s W T)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (f u ctx r dom cod fn arg k : OTerm α) :
    let L := guardedLeast (headerLeast (decorate (packedLeastProgram C X W s)))
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
  let L₀ := decorate (packedLeastProgram C X W s)
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast L₀) ctx cod seed k selected
  obtain ⟨head⟩ := exact_OpenLiteralHeaderLeastReport L₀ ctx cod seed k
    ⟨Derivation.conjunctionLeft atom⟩
  have actual : D B Γ (leastGraph C X W s ctx cod seed k) :=
    bridge.erase (packedLeastProgram C X W s) B α Γ ctx cod seed k ⟨Derivation.conjunctionLeft head⟩
  have cover := exact_OpenCoverageFromLeast C X W s ctx cod seed k actual
  exact ⟨gc,codTV,finiteCod,forms B α Γ ctx dom cod fn arg domT codT wf wu cover⟩

theorem exact_OpenDecoratedApplicationFormation (s : Settings) (P : List ProbeTy)
    (closed : ChildClosed P) (cv tv T : Program 1) (base : Program 2) (C : Program 3) (X : Program 2)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (f u ctx r dom cod fn arg k : OTerm α) :
    let W := coveredFormationWindow C s base T
    let L := guardedLeast (headerLeast (decorate (packedLeastProgram C X W s)))
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg) →
    D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) cod) ∧
    D B Γ (literalMembership (finiteCodes P) cod) ∧
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg)) :=
  exact_OpenDecoratedApplicationFormationWith s P closed cv tv T C (coveredFormationWindow C s base T) X
    (exact_OpenSimpleCoveredFormation C s base T) decorate bridge tvFit TFit included f u ctx r dom cod fn arg k

#print axioms exact_OpenSimpleCoveredFormation
#print axioms exact_OpenDecoratedApplicationFormationWith
#print axioms exact_OpenDecoratedApplicationFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedApplicationFormationProof
