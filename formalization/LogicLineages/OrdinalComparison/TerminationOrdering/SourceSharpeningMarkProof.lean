module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflexivityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningMarkProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening

theorem strictMarkPreservation : SourceSharpeningTargets.StrictMarkPreservation := by
  intro Symbol arity Gamma tau q u r h
  induction h using Sharp.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True)
  case var v => intro hm; cases hm
  case lam s t hs ih =>
    intro hm
    cases hq : strictMark s with
    | none => simp only [strictMark,hq,Option.map_none] at hm; cases hm
    | some sr =>
      simp only [strictMark,hq,Option.map_some] at hm
      have hr : MarkedTerm.lam sr=r := Option.some.inj hm
      subst r
      obtain ⟨v,hv,hsharp⟩ := ih sr hq
      exact ⟨.lam v,by simp only [strictMark,hv,Option.map_some],.lam sr v hsharp⟩
  case ordinary f ss ts hargs ih =>
    intro hm
    have hr : .marked f (headResult f) ss [] .nil=r := Option.some.inj hm
    subst r
    exact ⟨.marked f (headResult f) ts [] .nil,rfl,
      .marked f (headResult f) ss ts [] .nil [] .nil hargs (.nil f ss [] .nil)⟩
  case marked f tau ss ts sourceTypes sourceExtras targetTypes targetExtras hb he ihb ihe =>
    intro hm
    cases hm
  all_goals (intros; trivial)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningMarkProof
