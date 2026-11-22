module
public import LogicLineages.PermittedControl.OriginalMatrixPaidOrderRowTargets
import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeProof
import LogicLineages.PermittedControl.OriginalMatrixPaidOrderRowPreparationProof
import LogicLineages.PermittedControl.ActualPaidTerminalSignNormalizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
open ActualReadChargeIteration (RankBound)
open ActualFiniteGlobalTail (syntaxOf)
open ActualEffectiveGlobalTail (inputTailCode)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)
open MixedSameRankResidue (encodeWeighted)
open OriginalMatrixActualReadTape (exactRowState)
open ActualPaidTerminalSignNormalization (exactActualPaidTerminalSignNormalization)

theorem exactPaidSourceOrderRow : ExactPaidSourceOrderRow := by
  intro f B selected ρ strict r zRank row v positive _ actual ranks guardPaid signPaid
  obtain ⟨source,hit,rawValue⟩ := (exactRowState f ρ row v).mp actual.2.1
  let clean := stateAfterShort source
  obtain ⟨_,_,_,syn,constant,live,long,same⟩ :=
    exactSourceShortPreparation f B selected ρ row source hit
  have bounded : RankBound r zRank clean := by
    intro rd member
    have hm : rd.1 ∈ keptSyntax row.2.2 := by
      rw [← syn]
      exact List.mem_map.mpr ⟨rd,member,rfl⟩
    exact ranks rd.1 (List.mem_filter.mp hm).1
  have paid : ∀ t ∈ syntaxOf clean, inputTailCode B r ((syntaxOf clean).map encodeWeighted) ≤ ρ t.2.rank := by
    rw [syn]
    exact guardPaid
  have sign : inputSignBoundCode r clean.constant ((syntaxOf clean).map encodeWeighted) ≤ ρ zRank := by
    rw [syn,constant]
    exact signPaid
  obtain ⟨n,final,path,bound,terminal,finalLive,finalBound,ancestry,conserve⟩ :=
    exactActualPaidTerminalSignNormalization f B selected ρ strict r zRank clean live
      bounded long paid sign
  have value := conserve.symm.trans (same.trans rawValue)
  refine ⟨source,n,final,hit,rawValue,path,bound,terminal,finalLive,finalBound,?_,value,?_⟩
  · intro rd member
    obtain ⟨prior,hprior,hsame⟩ := ancestry rd member
    have hk : prior.1 ∈ keptSyntax row.2.2 := by
      rw [← syn]
      exact List.mem_map.mpr ⟨prior,hprior,rfl⟩
    exact ⟨prior.1,(List.mem_filter.mp hk).1,hsame⟩
  · rw [value]
    exact actual.2.2.1

end LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
