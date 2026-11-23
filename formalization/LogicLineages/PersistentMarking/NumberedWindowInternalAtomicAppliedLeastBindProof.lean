module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTypedNeutralEndpointCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastBindProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparseAppliedEndpointReportProof (endpointCases)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof (shapeRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (literalApplicationShape)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalTypedNeutralEndpointCasesProof (EndpointReports exact_OpenTypedNeutralEndpointCases)
open NumberedWindowInternalAtomicAppliedLeastShapeProof (ChosenAuxShape exact_OpenAtomicAppliedLeastShape)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem addressRename {β : Type} (c t k : OTerm α) (j : α → β) :
    (addressTerm c t k).relabel j = addressTerm (c.relabel j) (t.relabel j) (k.relabel j) := by
  simp only [addressTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

theorem exact_OpenSelectedAuxEndpointCases (least : Program 3) (σ τ : ProbeTy)
    (ctx cod raw y altCtx funTy head arg : OTerm α) (goal : Formula α)
    (picked : Nonempty (Derivation B Γ (outputReport least ctx cod raw y)))
    (arr : Nonempty (Derivation B Γ (equal funTy (numeral (typeCode (.arrow σ τ))))))
    (shape : Nonempty (Derivation B Γ (literalApplicationShape altCtx funTy head arg y)))
    (next : ∀ (δ : Type) (ρ : α → δ) (Θ : List (Formula δ)) (sel dom altCod a a' : OTerm δ),
      (∀ f ∈ Γ, f.relabel ρ ∈ Θ) →
      Nonempty (Derivation B Θ (programGraph least (suc sel) ![ctx.relabel ρ,cod.relabel ρ,raw.relabel ρ])) →
      EndpointReports B Θ σ τ (altCtx.relabel ρ) (head.relabel ρ) (arg.relabel ρ) (y.relabel ρ)
        dom altCod a a' →
      ChosenAuxShape B Θ (ctx.relabel ρ) (cod.relabel ρ) sel (altCtx.relabel ρ) dom altCod (head.relabel ρ) a' →
      Nonempty (Derivation B Θ (goal.relabel ρ))) :
    Nonempty (Derivation B Γ goal) := by
  apply endpointCases least ctx cod raw y goal picked
  intro β j Δ sel keep actual output _
  have declared := renameInto arr j Δ keep
  have exactArr : Nonempty (Derivation B Δ (equal (funTy.relabel j) (numeral (typeCode (.arrow σ τ))))) := by
    simpa only [equalEqn,eqnRelabel,ID1Completion.GuardedSourceSyntaxProof.numeralRename] using declared
  have h := renameInto shape j Δ keep
  rw [shapeRename] at h
  apply exact_OpenTypedNeutralEndpointCases σ τ (altCtx.relabel j) (funTy.relabel j)
    (head.relabel j) (arg.relabel j) (y.relabel j) exactArr h (goal.relabel j)
  intro δ k Θ dom altCod a a' retain reports
  let ρ := k ∘ j
  have chosen := renameInto actual k Θ retain
  rw [graph3Rename,sucRelabel] at chosen
  have value := renameInto output k Θ retain
  rw [eqnRelabel,addressRename] at value
  have e := exact_OpenAtomicAppliedLeastShape ((y.relabel j).relabel k) ((ctx.relabel j).relabel k)
    ((cod.relabel j).relabel k) (sel.relabel k) ((altCtx.relabel j).relabel k)
    dom altCod ((head.relabel j).relabel k) a' value reports.endpoint
  rw [formulaRelabelComposition j k goal]
  exact next δ ρ Θ (sel.relabel k) dom altCod a a' (keepThrough j k keep retain)
    (by simpa only [ρ,Term.relabel_relabel] using chosen)
    (by simpa only [ρ,Term.relabel_relabel] using reports)
    (by simpa only [ρ,Term.relabel_relabel] using e)

#print axioms exact_OpenSelectedAuxEndpointCases
end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastBindProof
