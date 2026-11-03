module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticPropertiesProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison
open FiniteOrdinaryBetaDiagnostic

theorem finitePrecedence : FiniteOrdinaryBetaDiagnosticTargets.ActualFinitePrecedence := by
  refine ⟨?_,?_,?_,?_⟩
  · intro f g k hfg hgk
    exact Nat.lt_trans hgk hfg
  · intro f
    exact Nat.lt_irrefl f.val
  · intro f g hfg
    have hv : f.val≠g.val := fun he => hfg (Fin.ext he)
    change g.val<f.val ∨ f.val<g.val
    omega
  · exact InvImage.wf Fin.val Nat.lt_wfRel.wf

theorem confinedWitness : FiniteOrdinaryBetaDiagnosticTargets.ActualFiniteConfinedWitness := by
  have steps := FiniteOrdinaryBetaDiagnosticStepsProof.ordinarySteps
  have htp : typeSupport tOriginal ⊆ typeSupport pOriginal := by decide
  have hut : typeSupport uOriginal ⊆ typeSupport tOriginal := by decide
  exact ⟨⟨steps.1,htp⟩,⟨steps.2,hut⟩,fun hpu => FiniteOrdinaryBetaDiagnosticProof.ordinaryFailure hpu.1⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticPropertiesProof
