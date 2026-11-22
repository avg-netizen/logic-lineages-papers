module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets
import LogicLineages.PermittedControl.ActualReadChargeIterationProgressProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualReadChargeIteration
open ActualZeroClassReplacement ActualZeroClassOutputState

private theorem traceSnoc {f : Nat → Nat} {B : Nat} {ρ : Nat → Nat} {r zRank n : Nat}
    {a b c : ReadState} (path : Trace f B ρ r zRank n a b) :
    ZeroEdge f B ρ r zRank b c → Trace f B ρ r zRank (n+1) a c := by
  induction path with
  | nil state =>
      intro edge
      exact .cons edge (.nil c)
  | cons first rest ih =>
      intro edge
      exact .cons first (ih edge)

private theorem originalRanksTrans {xs ys zs : List Read}
    (left : OriginalRanks xs ys) (right : OriginalRanks ys zs) : OriginalRanks xs zs := by
  intro rd member
  obtain ⟨middle,inMiddle,atMiddle⟩ := right rd member
  obtain ⟨first,inFirst,atFirst⟩ := left middle inMiddle
  exact ⟨first,inFirst,atMiddle.trans atFirst⟩

theorem exactReadChargeIteration : ExactReadChargeIteration := by
  intro f B selected ρ strict r zRank initial initialReads initialRank supplied
  have finish : ∀ fuel (n : Nat) (source : ReadState),
      Trace f B ρ r zRank n initial source →
      liftedReads f ρ source.reads → RankBound r zRank source →
      stateCharge r source ≤ fuel →
      ∃ (k : Nat) (final : ReadState), Trace f B ρ r zRank k source final ∧
        k ≤ fuel ∧ Terminal f ρ zRank final ∧ liftedReads f ρ final.reads ∧
        RankBound r zRank final ∧ OriginalRanks source.reads final.reads ∧
        stateValue source = stateValue final := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
        intro n source reached live bounded cost
        rcases exactReadProgress f B selected ρ strict r zRank source live bounded
            (supplied n source reached) with terminal | ⟨next, edge⟩
        · exact ⟨0,source,.nil source,Nat.zero_le _,terminal,live,bounded,
            fun rd hd => ⟨rd,hd,rfl⟩,rfl⟩
        · have nextReached := traceSnoc reached edge
          have nextBound : RankBound r zRank next := by
            intro rd member
            obtain ⟨old,oldMember,same⟩ := edge.ranks rd member
            rw [same]
            exact bounded old oldMember
          have nextCost : stateCharge r next < fuel := edge.strict.trans_le cost
          obtain ⟨k,final,tail,bound,stopped,finalLive,finalBound,ranks,value⟩ :=
            ih (stateCharge r next) nextCost (n+1) next nextReached edge.live nextBound le_rfl
          exact ⟨k+1,final,.cons edge tail,Nat.succ_le_of_lt (bound.trans_lt nextCost),
            stopped,finalLive,finalBound,originalRanksTrans edge.ranks ranks,
            edge.sameValue.trans value⟩
  exact finish (stateCharge r initial) 0 initial (.nil initial) initialReads initialRank le_rfl

theorem fullActualReadChargeIteration : FullActualReadChargeIteration :=
  ⟨exactReadProgress,exactReadChargeIteration⟩

end LogicLineages.PermittedControl.ActualReadChargeIteration
