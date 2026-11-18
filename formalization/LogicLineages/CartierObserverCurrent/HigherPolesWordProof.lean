module
public import LogicLineages.CartierObserverCurrent.HigherPolesWordTargets
public meta import LogicLineages.Audit
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.HigherPolesWord
theorem repeatedWord : Targets.RepeatedWord.{u} := by
  intro K _ _ _ f j
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, MixedWord.execute, MixedProper.step, if_true]
    rw [ih, Function.iterate_succ_apply]


#audit_namespace LogicLineages.CartierObserverCurrent.HigherPolesWord
end LogicLineages.CartierObserverCurrent.HigherPolesWord
