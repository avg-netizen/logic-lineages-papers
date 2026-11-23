module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedPathPrependProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets
open NumberedWindowInternalSparseTypedRawLiftChecks (exact_OpenInstalledTypedRaw5LiftedSingleton)
open NumberedWindowInternalSparseAddressTransitivityChecks (exact_InstalledAddressTransitivity)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume provide suppliedEdgeRename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportRename auxiliaryRename)
open NumberedWindowInternalSparseAppliedEndpointReportProof (endpointCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)

attribute [local irreducible] programGraph

private theorem liftRename {α β : Type} (root other W : Program 3) (V : Program 1)
    (ctx dom cod arg f w g : OTerm α) (j : α → β) :
    (liftInputs root other W V ctx dom cod arg f w g).relabel j =
      liftInputs root other W V (ctx.relabel j) (dom.relabel j) (cod.relabel j)
        (arg.relabel j) (f.relabel j) (w.relabel j) (g.relabel j) := by
  simp only [liftInputs,conjunctionRename]
  rw [graph5Rename,rawConsRename,sucRelabel,zRelabel]
  simp only [liftedEndpointGuards,conjunctionRename,programRename,
    NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.inputsRename,tripleInputsRename,
    auxiliaryRename,sucRelabel,zRelabel]

/-- A genuine raw function hop with the actual new syntax/typing guards and
both canonical application output reports supplies the original positive
certificate in the same unrefined physical body. -/
theorem appliedHop (i j cv tv : Program 1) (d root other W least : Program 3) (V : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f w g left middle : OTerm α) :
    let raw := typedRaw5 root other W V
    let r := addressPositive cv tv raw least
    let B := sourceBody (data i j r d) c
    Nonempty (Derivation B Γ (liftInputs root other W V ctx dom cod arg f w g)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod f arg) left)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod g arg) middle)) →
    Nonempty (Derivation B Γ (suppliedEdge r left middle)) := by
  intro raw r B lifted context result first last
  apply endpointCases least ctx cod (auxiliaryTerm dom cod f arg) left _ first
  intro β h Δ start keep firstLeast firstEq firstAddr
  have lw := renameInto lifted h Δ keep
  rw [liftRename] at lw
  have ctxW := renameInto context h Δ keep
  have codW := renameInto result h Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at ctxW codW
  have finish := renameInto last h Δ keep
  rw [reportRename,auxiliaryRename] at finish
  rw [suppliedEdgeRename]
  apply endpointCases least (ctx.relabel h) (cod.relabel h)
    (auxiliaryTerm (dom.relabel h) (cod.relabel h) (g.relabel h) (arg.relabel h)) (middle.relabel h) _ finish
  intro γ k Θ target keepMore lastLeast lastEq lastAddr
  rw [auxiliaryRename] at lastLeast
  have l2 := renameInto lw k Θ keepMore
  rw [liftRename] at l2
  have cv2 := renameInto ctxW k Θ keepMore
  have tv2 := renameInto codW k Θ keepMore
  simp only [unaryRename,sucRelabel,zRelabel] at cv2 tv2
  have lAddr := renameInto firstAddr k Θ keepMore
  rw [addressReportRename] at lAddr
  have lLeast := renameInto firstLeast k Θ keepMore
  simp only [programRename,tripleInputsRename,auxiliaryRename,sucRelabel] at lLeast
  rw [suppliedEdgeRename]
  let cx := (ctx.relabel h).relabel k
  let dm := (dom.relabel h).relabel k
  let cd := (cod.relabel h).relabel k
  let a := (arg.relabel h).relabel k
  let src := (f.relabel h).relabel k
  let dst := (g.relabel h).relabel k
  let child := (w.relabel h).relabel k
  let l := (left.relabel h).relabel k
  let m := (middle.relabel h).relabel k
  let s := start.relabel k
  have outs : Nonempty (Derivation B Θ
      (liftedSingletonFacts cv tv least l m cx cd s target
        (auxiliaryTerm dm cd src a) (auxiliaryTerm dm cd dst a))) := by
    obtain ⟨lp⟩ := lAddr
    obtain ⟨rp⟩ := lastAddr
    obtain ⟨cp⟩ := cv2
    obtain ⟨tp⟩ := tv2
    obtain ⟨ls⟩ := lLeast
    obtain ⟨rs⟩ := lastLeast
    exact ⟨Derivation.conjunctionIntroduction lp (Derivation.conjunctionIntroduction rp
      (Derivation.conjunctionIntroduction cp (Derivation.conjunctionIntroduction tp
        (Derivation.conjunctionIntroduction ls rs))))⟩
  obtain ⟨x⟩ := l2
  obtain ⟨y⟩ := outs
  have one := NumberedWindowInternalSparseTypedRawLiftChecks.exact_OpenInstalledTypedRaw5LiftedSingleton
    i j cv tv d root other W least V c γ Θ l m cx dm cd s target a src child dst
  obtain ⟨rule⟩ := one
  exact provide r l (singletonCertificate target (auxiliaryTerm dm cd src a) (functionWitnessTerm child)
    (auxiliaryTerm dm cd dst a)) m ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction x y)⟩

/-- Prepend the lifted real function hop to a real already-positive
application tail. Transitivity constructs the actual composite certificate,
not just a pair of independently accepted tapes. -/
theorem prependApplied (i j cv tv : Program 1) (d root other W least : Program 3) (V : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f w g left middle tail right : OTerm α) :
    let raw := typedRaw5 root other W V
    let r := addressPositive cv tv raw least
    let B := sourceBody (data i j r d) c
    Nonempty (Derivation B Γ (liftInputs root other W V ctx dom cod arg f w g)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod f arg) left)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod g arg) middle)) →
    Nonempty (Derivation B Γ (accepts r middle tail right)) →
    Nonempty (Derivation B Γ (suppliedEdge r left right)) := by
  intro raw r B lifted context result first last suffix
  have edge := appliedHop i j cv tv d root other W least V c α Γ ctx dom cod arg f w g left middle
    lifted context result first last
  apply consume r left middle _ edge
  intro β h Δ cert keep headCert
  have rest := renameInto suffix h Δ keep
  rw [NumberedWindowInternalPullbackSyntaxProof.acceptsRename] at rest
  rw [suppliedEdgeRename]
  obtain ⟨p⟩ := headCert
  obtain ⟨s⟩ := rest
  exact closedApply (exact_InstalledAddressTransitivity i j cv tv d raw least c β
    (left.relabel h) cert (middle.relabel h) (tail.relabel h) (right.relabel h))
    ⟨Derivation.conjunctionIntroduction p s⟩

#print axioms appliedHop
#print axioms prependApplied
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedPathPrependProof
