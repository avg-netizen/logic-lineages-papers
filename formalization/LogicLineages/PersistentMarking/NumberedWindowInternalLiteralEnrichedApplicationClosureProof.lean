module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationFormationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationScalarProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationNeutralOutputProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationClosureProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (existsOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralEnrichedApplicationScalarProof (exact_OpenEnrichedApplicationScalar)
open NumberedWindowInternalLiteralEnrichedApplicationFormationProof (exact_OpenEnrichedApplicationFormation)
open NumberedWindowInternalLiteralDecoratedApplicationFormationProof (OpenAuxFormation)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalLiteralApplicationNeutralOutputProof (exact_OpenLiteralApplicationNeutralOutput)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteCodes finiteScalar exact_MakeLiteralFiniteScalar)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (OpenDecorator)
open NumberedWindowInternalLiteralApplicationCoverageWindowProof (coveredFormationWindow)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

private theorem carrierAtReport (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (cv tv T : Program 1) (C W : Program 3) (E : Program 4) (forms : OpenAuxFormation C s W T)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (ends : WindowEndpoints W E) (paid : Preserves E (packedLeastOn C E s))
    (raw : Program 5) (c : Nat) (f u y ctx r dom cod fn arg : OTerm α) :
    let L := guardedLeast (headerLeast (decorate (packedLeastOn C E s)))
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg) →
    D B Γ (outputReport L ctx cod (auxiliaryTerm dom cod fn arg) y) →
    D B Γ (carrier data false c y) := by
  intro L i R data B left right inputs out
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ctx' := ctx.relabel j
  let cod' := cod.relabel j
  let y' := y.relabel j
  let A := programGraph L (suc k) ![ctx',cod',(auxiliaryTerm dom cod fn arg).relabel j] ⊓
    eqn y' (addressTerm ctx' cod' k)
  let Δ := A :: Γ.map weaken
  have keep (φ : Formula α) (h : φ ∈ Γ) : φ.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,h,rfl⟩)
  have one := renameInto left j Δ keep
  have two := renameInto right j Δ keep
  have parsed := renameInto inputs j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at one two
  rw [inputsRename] at parsed
  have row : Derivation B Δ A := Derivation.hypothesis List.mem_cons_self
  have least : D B Δ (programGraph L (suc k) ![ctx',cod',(auxiliaryTerm dom cod fn arg).relabel j]) :=
    ⟨Derivation.conjunctionLeft row⟩
  rw [auxiliaryRename] at least
  obtain ⟨gc,gt,finite,formed⟩ := exact_OpenEnrichedApplicationFormation s P closed cv tv T C W E forms decorate bridge
    tvFit TFit included (f.relabel j) (u.relabel j) ctx' (r.relabel j) (dom.relabel j) cod'
    (fn.relabel j) (arg.relabel j) k one two parsed least
  have old := exact_OpenEnrichedApplicationScalar cv tv C W E s decorate bridge ends paid ctx' cod' _ k y'
    gc gt formed least ⟨Derivation.conjunctionRight row⟩
  obtain ⟨_,_,reported,_⟩ := literalAddress (body := B) (Γ := Δ) ctx' cod' k
  have field := headTransport rawResult cod' (addressTerm ctx' cod' k) y' ![]
    ⟨symm (Derivation.conjunctionRight row)⟩ reported
  have scalar : D B Δ (unary i (suc z) y') :=
    exact_MakeLiteralFiniteScalar (addressScalar cv tv W L) (finiteCodes P) y' cod' field old finite
  let edge := addressPositive cv tv R L
  have actual : D B Δ ((carrier data false c y).relabel j) := by
    rw [carrierRename]
    exact (exact_DomainRules i (jRaw i) edge (dCore i edge permutation) false c B _ Δ y').2 scalar
  obtain ⟨rule⟩ := actual
  obtain ⟨report⟩ := out
  exact ⟨Derivation.existentialElimination report rule⟩

/-- Both application-closure conclusions for the actual finite-scalar
program and actual forming window. The least, scalar and raw slots
are all named ASTs. Only finite type support assumptions and the
underlying paired edge comparison are requested. -/
theorem exact_OpenEnrichedApplicationClosure (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (cv tv T : Program 1) (C W : Program 3) (E : Program 4) (forms : OpenAuxFormation C s W T)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (ends : WindowEndpoints W E) (paid : Preserves E (packedLeastOn C E s))
    (raw : Program 5) (c : Nat) (f u y : OTerm α) :
    let L := guardedLeast (headerLeast (decorate (packedLeastOn C E s)))
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) →
    D B Γ (carrier data false c y) ∧ D B Γ (atom neutralSource y) := by
  intro L i R data B accepted
  refine ⟨?_,exact_OpenLiteralApplicationNeutralOutput i (decorate (packedLeastOn C E s)) f u y accepted⟩
  obtain ⟨row⟩ := forward i L f u y accepted
  let h := Derivation.conjunctionRight row
  have left : D B Γ (unary i (suc z) f) := ⟨Derivation.conjunctionLeft row⟩
  have right : D B Γ (unary i (suc z) u) := ⟨Derivation.conjunctionLeft h⟩
  apply rowCases L f u y (carrier data false c y) ⟨Derivation.conjunctionRight h⟩
  intro β j Δ ctx r dom cod fn arg keep known
  rw [carrierRename]
  have one := renameInto left j Δ keep
  have two := renameInto right j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at one two
  obtain ⟨pair⟩ := known
  exact carrierAtReport s P closed cv tv T C W E forms decorate bridge tvFit TFit included ends paid
    raw c (f.relabel j) (u.relabel j) (y.relabel j) ctx r dom cod fn arg one two
    ⟨Derivation.conjunctionLeft pair⟩ ⟨Derivation.conjunctionRight pair⟩


#print axioms exact_OpenEnrichedApplicationClosure
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationClosureProof
