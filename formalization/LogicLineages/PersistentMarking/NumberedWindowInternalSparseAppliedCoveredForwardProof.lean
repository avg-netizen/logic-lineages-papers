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

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedOneHopForwardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedCoveredForwardProof
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


open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open NumberedWindowInternalPullbackTargets (forwardImage)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (coveredWindow exact_CoveredWindowReport)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseAppliedOneHopForwardProof (forwardFromLeast)
open NumberedWindowScalarAlgorithm (Settings)

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

private theorem edgeRename {α β : Type} (S : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge S false c x y).relabel j = edge S false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S false c x y).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

private theorem forwardRename {α β : Type} (S : Data) (p : Program 3) (c : Nat)
    (g u x : OTerm α) (j : α → β) :
    (forwardImage S p c g u x).relabel j =
      forwardImage S p c (g.relabel j) (u.relabel j) (x.relabel j) := by
  unfold forwardImage
  rw [existsRename,conjunctionRename,acceptsRename,edgeRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

/-- A real selected post-hop least is opened in the object calculus. No
destination class or result term is supplied by the external caller. -/
theorem forwardFromHasLeast (i j cv tv : Program 1) (d root other W C : Program 3)
    (X : Program 2) (s : Settings) (V : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f w g gAddr u result left : OTerm α) :
    let least := packedLeastProgram C X W s
    let raw := typedRaw5 root other W V
    let r := addressPositive cv tv raw least
    let S := data i j r d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (liftInputs root other W V ctx dom cod arg f w g)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod f arg) left)) →
    Nonempty (Derivation B Γ (unary i (suc z) gAddr)) →
    Nonempty (Derivation B Γ (unary i (suc z) u)) →
    Nonempty (Derivation B Γ (parsedApplicationInputs gAddr u ctx result dom cod g arg)) →
    Nonempty (Derivation B Γ (hasLeast C X W s ctx cod (auxiliaryTerm dom cod g arg))) →
    Nonempty (Derivation B Γ (forwardImage S (applicationGuard i least) c gAddr u left)) := by
  intro least raw r S B lifted cvOK tvOK first gOK uOK parsed existsLeast
  apply casesLeast C X W s ctx cod (auxiliaryTerm dom cod g arg) _ existsLeast
  intro β h Δ k keep exactLeast
  have hw := renameInto lifted h Δ keep
  rw [liftRename] at hw
  have cv' := renameInto cvOK h Δ keep
  have tv' := renameInto tvOK h Δ keep
  have fg := renameInto gOK h Δ keep
  have fu := renameInto uOK h Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at cv' tv' fg fu
  have a := renameInto first h Δ keep
  rw [reportRename,auxiliaryRename] at a
  have row := renameInto parsed h Δ keep
  rw [inputsRename] at row
  rw [forwardRename]
  have call : Nonempty (Derivation B Δ (programGraph least (suc k)
      ![ctx.relabel h,cod.relabel h,(auxiliaryTerm dom cod g arg).relabel h])) := exactLeast
  rw [auxiliaryRename] at call
  exact forwardFromLeast i j cv tv d root other W least V c β Δ
    (ctx.relabel h) (dom.relabel h) (cod.relabel h) (arg.relabel h)
    (f.relabel h) (w.relabel h) (g.relabel h) (gAddr.relabel h) (u.relabel h)
    (result.relabel h) (left.relabel h) k hw cv' tv' a fg fu row call

/-- On the physical covered-window AST the outgoing raw window report itself
supplies the final real least, after which the canonical image is derived.
The endpoint parser, scalar, and typed raw-hop facts are still actual premises. -/
theorem forwardFromCoveredWindow (i j cv tv : Program 1) (d root other baseW C : Program 3)
    (X : Program 2) (s : Settings) (V : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f w g gAddr u result left : OTerm α) :
    let W := coveredWindow C s baseW
    let least := packedLeastProgram C X W s
    let raw := typedRaw5 root other W V
    let r := addressPositive cv tv raw least
    let S := data i j r d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (liftInputs root other W V ctx dom cod arg f w g)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod f arg) left)) →
    Nonempty (Derivation B Γ (unary i (suc z) gAddr)) →
    Nonempty (Derivation B Γ (unary i (suc z) u)) →
    Nonempty (Derivation B Γ (parsedApplicationInputs gAddr u ctx result dom cod g arg)) →
    Nonempty (Derivation B Γ (forwardImage S (applicationGuard i least) c gAddr u left)) := by
  intro W least raw r S B typed cvOK tvOK first gOK uOK row
  obtain ⟨real⟩ := typed
  let dest := auxiliaryTerm dom cod g arg
  have good : Derivation B Γ (windowAt W ctx cod dest) :=
    Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight real))
  obtain ⟨expand⟩ := exact_CoveredWindowReport C X s baseW B α Γ ctx cod dest
  have windowFacts := Derivation.implicationElimination expand good
  exact forwardFromHasLeast i j cv tv d root other W C X s V c α Γ ctx dom cod arg f w g
    gAddr u result left ⟨real⟩ cvOK tvOK first gOK uOK row
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight windowFacts)⟩

#print axioms forwardFromHasLeast
#print axioms forwardFromCoveredWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedCoveredForwardProof
