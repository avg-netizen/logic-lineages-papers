module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastBindProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreeAppliedLeastProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (freeTerm literalApplicationShape)
open NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof (shapeRename)
open NumberedWindowInternalAtomicApplicationShapeObjectChecks
  (exact_OpenAtomicApplicationShape exact_OpenApplicationForgets)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalTypedNeutralEndpointCasesProof (EndpointReports)
open NumberedWindowInternalAtomicAppliedLeastShapeProof (ChosenAuxShape)
open NumberedWindowInternalAtomicAppliedLeastBindProof (exact_OpenSelectedAuxEndpointCases)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A single genuine shape-refined physical application is used twice:
peeling its unchanged frontend exposes its actual chosen least call,
while the real shape test reports the original free-headed output. The
two reports identify the representative of the same y via functionality. -/
theorem exact_OpenFreeAppliedSelectedLeast (i : Program 1) (least : Program 3) (σ τ : ProbeTy)
    (f arg out freeCtx ty name : OTerm α) (goal : Formula α)
    (declared : Nonempty (Derivation B Γ (equal ty (numeral (typeCode (.arrow σ τ))))))
    (literalFree : Nonempty (Derivation B Γ (equal f (packedFreeTerm freeCtx ty name))))
    (held : Nonempty (Derivation B Γ (accepts (refinedApplication (applicationGuard i least)) f arg out)))
    (next : ∀ (δ : Type) (ρ : α → δ) (Θ : List (Formula δ))
      (ctx dom cod fn a0 selected d t a a' : OTerm δ),
      (∀ p ∈ Γ, p.relabel ρ ∈ Θ) →
      Nonempty (Derivation B Θ (programGraph least (suc selected) ![ctx,cod,auxiliaryTerm dom cod fn a0])) →
      EndpointReports B Θ σ τ (freeCtx.relabel ρ) ((freeTerm ty name).relabel ρ)
        (arg.relabel ρ) (out.relabel ρ) d t a a' →
      ChosenAuxShape B Θ ctx cod selected (freeCtx.relabel ρ) d t ((freeTerm ty name).relabel ρ) a' →
      Nonempty (Derivation B Θ (goal.relabel ρ))) :
    Nonempty (Derivation B Γ goal) := by
  let p := applicationGuard i least
  let head := freeTerm ty name
  have shape := exact_OpenAtomicApplicationShape.1 p B α Γ f arg out freeCtx ty name literalFree held
  have old := exact_OpenApplicationForgets p B α Γ f arg out held
  obtain ⟨seen⟩ := forward i least f arg out old
  apply rowCases least f arg out goal ⟨Derivation.conjunctionRight (Derivation.conjunctionRight seen)⟩
  intro β j Δ ctx _ dom cod fn a0 keep row
  obtain ⟨fields⟩ := row
  have h := renameInto shape j Δ keep
  rw [shapeRename] at h
  have hTy := renameInto declared j Δ keep
  have arr : Nonempty (Derivation B Δ (equal (ty.relabel j) (numeral (typeCode (.arrow σ τ))))) := by
    simpa only [equalEqn,eqnRelabel,numeralRename] using hTy
  apply exact_OpenSelectedAuxEndpointCases least σ τ ctx cod (auxiliaryTerm dom cod fn a0)
    (out.relabel j) (freeCtx.relabel j) (ty.relabel j) (head.relabel j) (arg.relabel j)
    (goal.relabel j) ⟨Derivation.conjunctionRight fields⟩ arr h
  intro δ k Θ selected d t a a' retain computed endpoint aligned
  rw [formulaRelabelComposition j k goal]
  let ρ := k ∘ j
  exact next δ ρ Θ (ctx.relabel k) (dom.relabel k) (cod.relabel k) (fn.relabel k) (a0.relabel k)
    selected d t a a' (keepThrough j k keep retain)
    (by simpa only [auxiliaryRename] using computed)
    (by simpa only [head,ρ,Term.relabel_relabel] using endpoint)
    (by simpa only [head,ρ,Term.relabel_relabel] using aligned)

#print axioms exact_OpenFreeAppliedSelectedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalFreeAppliedLeastProof
