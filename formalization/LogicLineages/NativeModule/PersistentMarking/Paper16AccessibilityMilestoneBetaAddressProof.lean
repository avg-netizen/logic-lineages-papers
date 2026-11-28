module
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaTargetProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedResultProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectPhysicalReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneBetaAddressProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier carrierProgram)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
  (numeralNeApply)
open ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof (carrierGraph)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalProbeTargets (typeCode typedAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports)
open NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof (actualArrowFields)
open NumberedWindowInternalFreshProbeParsedTypedResultProof (openResult)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof (BetaJoinedRulesAt)
open NumberedWindowInternalLiteralDirectPhysicalReportProof (exact_OpenDirectPhysicalReportCases)
open NumberedWindowInternalLiteralAlignedBetaTargetProof (exact_OpenAlignedBetaTarget)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy} {α : Type}
variable {Γ : List (Formula α)}

abbrev installedHop (A : InstalledWindow S K W) : Program 3 :=
  hop A.contextGuard A.typeGuard
    (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least

private theorem addressTypeReport {B : PositiveArithmeticOperators.Positive (Fin 1)}
    (q ctx ty k : OTerm α) (held : D B Γ (addressReport q ctx ty k)) :
    D B Γ (programGraph rawResult ty ![q]) := by
  obtain ⟨report⟩ := held
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight report))⟩

/-- The original direct report gives the same type at both endpoints.
If the original application result is typed, the actual beta row's
target report therefore carries the requested numeral. -/
theorem exact_OpenInstalledBetaDirectTypeField (A : InstalledWindow S K W) (c : Nat)
    (τ : Ty) (x y sc st after : OTerm α)
    (typedSource : D (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes W) (formulaType τ) x))
    (step : D (sourceBody A.presentation c) Γ (direct A.presentation (installedHop A) c x y))
    (target : D (sourceBody A.presentation c) Γ (addressReport y sc st after)) :
    D (sourceBody A.presentation c) Γ (eqn st (numeral (typeCode (formulaType τ)))) := by
  let R := rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least
  let B := sourceBody A.presentation c
  let expected : OTerm α := numeral (typeCode (formulaType τ))
  apply exact_OpenDirectPhysicalReportCases A.scalar A.contextGuard A.typeGuard R A.least
    c x y (eqn st expected) step
  intro β j Δ _ ctx ty before last keep left right _ _ _
  have typed : D B Δ (typedAt (chosenH A.probes W) (formulaType τ) (x.relabel j)) := by
    simpa only [typedRename] using renameInto typedSource j Δ keep
  have actual := openResult A.probes W (formulaType τ) B β Δ (x.relabel j) ty typed
    (addressTypeReport (x.relabel j) ctx ty before left)
  rw [equalEqn] at actual
  obtain ⟨actual⟩ := actual
  have moved : D B Δ (addressReport (y.relabel j) (sc.relabel j) (st.relabel j) (after.relabel j)) := by
    simpa only [addressReportRename] using renameInto target j Δ keep
  obtain ⟨same⟩ := valueUnique rawResult (st.relabel j) ty ![y.relabel j]
    (addressTypeReport (y.relabel j) (sc.relabel j) (st.relabel j) (after.relabel j) moved)
    (addressTypeReport (y.relabel j) ctx ty last right)
  simp only [expected,eqnRelabel,numeralRename]
  exact ⟨trans same actual⟩

/-- The original guarded application's decoded codomain is the requested
codomain of the typed function. The aligned direct step supplies its
target type field at that same codomain. -/
theorem exact_OpenInstalledBetaApplicationTypeField (A : InstalledWindow S K W) (c : Nat)
    (σ τ : Ty) (x u ctx result dom cod fn arg st : OTerm α)
    (functionTyped : D (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes W) (formulaType (.arrow σ τ)) x))
    (parsed : D (sourceBody A.presentation c) Γ
      (parsedApplicationInputs x u ctx result dom cod fn arg))
    (sameType : D (sourceBody A.presentation c) Γ (eqn st cod)) :
    D (sourceBody A.presentation c) Γ (eqn st (numeral (typeCode (formulaType τ)))) := by
  let B := sourceBody A.presentation c
  obtain ⟨parsed⟩ := parsed
  unfold parsedApplicationInputs addressReports at parsed
  let fields := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight parsed))
  let resultFields := Derivation.conjunctionLeft fields
  have resultGraph : D B Γ (programGraph rawResult result ![x]) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight resultFields)⟩
  let equalities := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight fields))
  have shape : D B Γ (eqn result (rawCons dom cod)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight equalities)⟩
  have requested := openResult A.probes W (formulaType (.arrow σ τ)) B α Γ x result
    functionTyped resultGraph
  obtain ⟨parts⟩ := actualArrowFields (formulaType σ) (formulaType τ) result dom cod requested
    (by rw [equalEqn]; exact shape)
  have numeric : D B Γ (eqn cod (numeral (typeCode (formulaType τ)))) := by
    rw [← equalEqn]
    exact ⟨Derivation.conjunctionRight parts⟩
  obtain ⟨same⟩ := sameType
  obtain ⟨numeric⟩ := numeric
  exact ⟨trans same numeric⟩

/-- The installed finite typing split pays the requested probe type
when the parsed result field equals that type's literal code. -/
theorem exact_OpenInstalledCarrierRequestedType (A : InstalledWindow S K W) (c : Nat)
    (cases : CarrierTypingCases A c) (τ : Ty) (q st : OTerm α)
    (held : D (sourceBody A.presentation c) Γ (carrier A.presentation false c q))
    (reported : D (sourceBody A.presentation c) Γ (programGraph rawResult st ![q]))
    (coordinate : D (sourceBody A.presentation c) Γ
      (eqn st (numeral (typeCode (formulaType τ))))) :
    D (sourceBody A.presentation c) Γ (typedAt (chosenH A.probes W) (formulaType τ) q) := by
  let B := sourceBody A.presentation c
  let goal := typedAt (chosenH A.probes W) (formulaType τ) q
  apply cases α Γ q goal held
  intro σ _
  let branch := typedAt (chosenH A.probes W) (formulaType σ) q
  have candidate : D B (branch :: Γ) branch := ⟨Derivation.hypothesis List.mem_cons_self⟩
  by_cases code : typeCode (formulaType σ) = typeCode (formulaType τ)
  · simpa only [branch,goal,typedAt,code] using candidate
  · obtain ⟨reported⟩ := reported
    obtain ⟨coordinate⟩ := coordinate
    have actual := openResult A.probes W (formulaType σ) B α (branch :: Γ) q st candidate
      ⟨addHyp reported branch⟩
    rw [equalEqn] at actual
    obtain ⟨actual⟩ := actual
    have conflict := trans (symm actual) (addHyp coordinate branch)
    exact ⟨Derivation.explosion (numeralNeApply _ _ code conflict)⟩

/-- At the original rebuilt beta address, recover the installed scalar
carrier and the requested probe type from the same direct reduct,
least graph, and type field of the aligned row. -/
theorem exact_OpenInstalledBetaRebuiltAddress (A : InstalledWindow S K W) (c : Nat)
    (τ : Ty) (L₀ : Program 3) (U : Program 2) (typing : CarrierTypingCases A c)
    (joined : BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (installedHop A) L₀ A.least U W A.probes c)
    {x ctx dom cod fn arg sc st after q r d e f a bind body y rebuilt : OTerm α}
    (step : D (sourceBody A.presentation c) Γ (direct A.presentation (installedHop A) c x y))
    (row : AlignedBetaRow L₀ A.least U (sourceBody A.presentation c) Γ
      ctx dom cod fn arg sc st after q r d e f a bind body y)
    (output : D (sourceBody A.presentation c) Γ (eqn (suc r) (suc rebuilt)))
    (typeField : D (sourceBody A.presentation c) Γ (eqn st (numeral (typeCode (formulaType τ))))) :
    D (sourceBody A.presentation c) Γ (carrier A.presentation false c (addressTerm sc st after)) ∧
    D (sourceBody A.presentation c) Γ (typedAt (chosenH A.probes W) (formulaType τ) (addressTerm sc st after)) ∧
    D (sourceBody A.presentation c) Γ (programGraph A.least (suc after) ![sc,st,rebuilt]) := by
  let B := sourceBody A.presentation c
  let actual := addressTerm sc st after
  obtain ⟨_,least,address⟩ := exact_OpenAlignedBetaTarget rebuilt row output
  have source := joined.arithmetic.directCarrier α Γ x y step
  have admitted : D B Γ (carrier A.presentation false c actual) := by
    rw [carrierGraph] at source ⊢
    exact exact_OpenInstanceBodyTransport (carrierProgram A.presentation false) (suc z)
      (numeral c) y actual address source
  have result : D B Γ (programGraph rawResult st ![actual]) :=
    (literalAddress (body := B) (Γ := Γ) sc st after).2.2.1
  exact ⟨admitted,exact_OpenInstalledCarrierRequestedType A c typing τ actual st admitted result typeField,least⟩

/-- The remaining computable-instance premise is applied only at the
actual reconstructed address in the installed window. The emitted
reduct then has the same computability formula. -/
theorem exact_OpenInstalledBetaRebuiltComputability (A : InstalledWindow S K W) (c : Nat)
    (τ : Ty) (L₀ : Program 3) (U : Program 2) (typing : CarrierTypingCases A c)
    (joined : BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (installedHop A) L₀ A.least U W A.probes c)
    {x ctx dom cod fn arg sc st after q r d e f a bind body y rebuilt : OTerm α}
    (step : D (sourceBody A.presentation c) Γ (direct A.presentation (installedHop A) c x y))
    (row : AlignedBetaRow L₀ A.least U (sourceBody A.presentation c) Γ
      ctx dom cod fn arg sc st after q r d e f a bind body y)
    (output : D (sourceBody A.presentation c) Γ (eqn (suc r) (suc rebuilt)))
    (typeField : D (sourceBody A.presentation c) Γ (eqn st (numeral (typeCode (formulaType τ)))))
    (instanceComputes :
      D (sourceBody A.presentation c) Γ (carrier A.presentation false c (addressTerm sc st after)) →
      D (sourceBody A.presentation c) Γ (typedAt (chosenH A.probes W) (formulaType τ) (addressTerm sc st after)) →
      D (sourceBody A.presentation c) Γ (programGraph A.least (suc after) ![sc,st,rebuilt]) →
      D (sourceBody A.presentation c) Γ
        (formula (applicationGuard A.scalar A.least) (formulaType τ) (addressTerm sc st after))) :
    D (sourceBody A.presentation c) Γ (formula (applicationGuard A.scalar A.least) (formulaType τ) y) := by
  obtain ⟨admitted,typed,_⟩ :=
    exact_OpenInstalledBetaRebuiltAddress A c τ L₀ U typing joined step row output typeField
  exact NumberedWindowInternalLiteralAlignedBetaTargetProof.exact_OpenComputabilityOfAlignedBetaTarget
    (applicationGuard A.scalar A.least) (formulaType τ) rebuilt row output
    (instanceComputes admitted typed)

#print axioms installedHop
#print axioms exact_OpenInstalledBetaDirectTypeField
#print axioms exact_OpenInstalledBetaApplicationTypeField
#print axioms exact_OpenInstalledCarrierRequestedType
#print axioms exact_OpenInstalledBetaRebuiltAddress
#print axioms exact_OpenInstalledBetaRebuiltComputability
end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneBetaAddressProof
