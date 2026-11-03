module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceSharpeningInversionProof

theorem unmarkedIdentityAt {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (u : MarkedTerm Symbol arity Gamma tau) (h : Unmarked Symbol arity Gamma u) :
    ∀ q : MarkedTerm Symbol arity Gamma tau,Sharp Symbol arity Gamma q u → q=u := by
  induction h using Unmarked.rec
    (motive_2 := fun Gamma types target _ => ∀ source : Arguments Symbol arity Gamma types,
      ArgumentsSharp Symbol arity Gamma source target → source=target)
  case var v => intro q h; cases h; rfl
  case lam body hu ih =>
    intro q h
    obtain ⟨src,he,hs⟩ := lambdaInversion q (.lam body) h _ _ body rfl
    have hq : q=MarkedTerm.lam src := by injection he
    rw [hq,ih src hs]
  case ordinary f base hu ih =>
    intro q h
    obtain ⟨src,he,hs⟩ := ordinaryInversion q (.ordinary f base) h f base rfl
    have hq : q=MarkedTerm.ordinary f src := by injection he
    rw [hq,ih src hs]
  case nil args h => cases args; rfl
  case cons q rest hq hr ihq ihr args h =>
    cases h with
    | cons src _ srcRest _ hs hrest =>
      exact congrArg₂ Arguments.cons (ihq src hs) (ihr srcRest hrest)

theorem unmarkedIdentity : SourceSharpeningReflectionTargets.UnmarkedIdentity := by
  intro Symbol arity Gamma tau q u hu hs
  exact unmarkedIdentityAt u hu q hs

theorem markabilityReflection : SourceSharpeningReflectionTargets.MarkabilityReflection := by
  intro Symbol arity Gamma tau q u v h
  induction h using Sharp.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True)
  case var x => intro hm; cases hm
  case lam s t hs ih =>
    intro hm
    cases ht : strictMark t with
    | none => simp only [strictMark,ht,Option.map_none] at hm; cases hm
    | some target =>
      simp only [strictMark,ht,Option.map_some] at hm
      have hv : MarkedTerm.lam target=v := Option.some.inj hm
      subst v
      obtain ⟨src,hsrc,hsharp⟩ := ih target ht
      exact ⟨.lam src,by simp only [strictMark,hsrc,Option.map_some],.lam src target hsharp⟩
  case ordinary f ss ts hargs ih =>
    intro hm
    have hv : .marked f (headResult f) ts [] .nil=v := Option.some.inj hm
    subst v
    exact ⟨.marked f (headResult f) ss [] .nil,rfl,
      .marked f (headResult f) ss ts [] .nil [] .nil hargs (.nil f ss [] .nil)⟩
  case marked f tau ss ts sourceTypes sourceExtras targetTypes targetExtras hb he ihb ihe =>
    intro hm
    cases hm
  all_goals (intros; trivial)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionProof
