module
public import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
open ActualCanonicalZeroTrace ActualCanonicalNodeProgress
open ActualReadChargeIteration (ReadState stateCharge)

theorem exactCanonicalProgressSplit : ExactCanonicalProgressSplit := by
  intro f B ρ r top s progress
  obtain ⟨xs,normal,live,inactive | ⟨active,step⟩⟩ := progress
  · exact Or.inl ⟨xs,normal,live,Or.inl inactive⟩
  · obtain ⟨a,anns,C,ν,listed,matched,packet,aligned,maxValue,floor,guards,ready,transfer,
      coeff,nonzero | ⟨_,out,witness,strict⟩⟩ := step
    · exact Or.inl ⟨xs,normal,live,Or.inr ⟨active,a,anns,C,ν,listed,matched,packet,
        aligned,maxValue,floor,guards,ready,transfer,coeff,nonzero⟩⟩
    · exact Or.inr ⟨a,out,witness,strict⟩

private theorem snoc {f B ρ r top answers s t u a}
    (path : CanonicalTrace f B ρ r top answers s t) :
    CanonicalZeroWitness f B ρ r top t u a →
    CanonicalTrace f B ρ r top (answers ++ [a]) s u := by
  induction path with
  | nil s =>
    intro edge
    exact .cons edge (.nil u)
  | cons earlier tail next =>
    intro edge
    exact .cons earlier (next edge)

theorem exactCanonicalStrictStopping : ExactCanonicalStrictStopping := by
  intro f B ρ r top initial progress
  have localStop : ∀ fuel (seen : List (List ActualFullLabelPairGuards.Answer)) (source : ReadState),
      CanonicalTrace f B ρ r top seen initial source → stateCharge r source ≤ fuel →
      ∃ (future : List (List ActualFullLabelPairGuards.Answer)) (final : ReadState),
        CanonicalTrace f B ρ r top future source final ∧ StopsAt f B ρ r top final := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro seen source path cost
      rcases exactCanonicalProgressSplit f B ρ r top source (progress seen source path) with
        stop | ⟨a,next,witness,strict⟩
      · exact ⟨[],source,.nil source,stop⟩
      · obtain ⟨rest,final,tail,stop⟩ :=
          ih (stateCharge r next) (strict.trans_le cost) (seen ++ [a]) next (snoc path witness) le_rfl
        exact ⟨a::rest,final,.cons witness tail,stop⟩
  exact localStop (stateCharge r initial) [] initial (.nil initial) le_rfl

end LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
