module
public import LogicLineages.PermittedControl.ActualPaidTerminalSignNormalizationTargets
import LogicLineages.PermittedControl.ActualEffectiveHighTailNormalizationProof
import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundDominanceProof
import LogicLineages.PermittedControl.ActualTraceSignCutoffProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidTerminalSignNormalization
open ActualReadChargeIteration ActualEffectiveHighTailNormalization
open ActualTraceSignCutoff ActualEffectiveTerminalSignBound

theorem exactActualPaidTerminalSignNormalization : ExactActualPaidTerminalSignNormalization := by
  intro f B selected ρ strict r zRank initial reads bounded long guardPaid signPaid
  obtain ⟨n,final,path,bound,terminal,finalReads,finalBound,ranks,value⟩ :=
    exactActualEffectiveHighTailNormalization f B selected ρ strict r zRank
      initial reads bounded long guardPaid
  refine ⟨n,final,path,bound,?_,finalReads,finalBound,ranks,value⟩
  obtain ⟨xs,normalized,kind⟩ := terminal
  refine ⟨xs,normalized,?_⟩
  rcases kind with linear | ⟨active,nonzero⟩
  · exact Or.inl linear
  · obtain ⟨annotations,C,chosen,coefficient,identity,error,conditional⟩ := nonzero
    obtain ⟨semantic,typed⟩ :=
      exactReachedCutoffDominance f B ρ r zRank n initial final path xs normalized
    have funded := (exactSignBoundDominance r initial).trans signPaid
    have semanticPaid := semantic.trans funded
    have typedPaid := typed.trans funded
    exact Or.inr ⟨active,annotations,C,chosen,coefficient,identity,error,
      semanticPaid,typedPaid,conditional semanticPaid⟩

end LogicLineages.PermittedControl.ActualPaidTerminalSignNormalization
