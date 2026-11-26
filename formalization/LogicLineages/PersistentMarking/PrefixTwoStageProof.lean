import LogicLineages.PersistentMarking.PrefixStageSupport
namespace LogicLineages.PersistentMarking.PrefixTwoStageProof
open Spine PrefixStageSupport

theorem staged (S : Signature) (f : Head) (ρ τ : Ty) (base extras : Args) (q : Expr) (values first second : Args) (r w : Expr)
    (hp : PaperTerm S (.marked f ρ base extras) ρ)
    (hv : PrefixCopies f base extras values) (hf : PrefixCopies f base extras first) (hs : PrefixCopies f base extras second)
    (hw : w.type = τ) (hfirst : applyAux q first values = some r) (hsecond : apply r second = some w) :
    applyAux q (first.append second) values = some w ∨ Refines S (.marked f τ base extras) w := by
  cases first with
  | nil =>
    simp only [applyAux,Option.some.injEq] at hfirst
    subst r
    cases second with
    | nil => exact Or.inl (by simpa only [apply,applyAux,Args.append] using hsecond)
    | cons b bs =>
      have hh := PrefixSplicingProof.splice S f ρ τ base extras q .nil values (.cons b bs) w hp hv hs hw hsecond
      exact hh.elim Or.inl (fun he => Or.inr he.2)
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux] at hfirst
    | bound σ i => simp [applyAux] at hfirst
    | lam σ body =>
      by_cases ht : a.type = σ
      · have hc : applyAux body rest (.cons a values) = some r := by simpa only [applyAux,ht,if_true] using hfirst
        cases hf with
        | cons ha hr =>
          have hh := staged S f ρ τ base extras body (.cons a values) rest second r w hp (.cons ha hv) hr hs hw hc hsecond
          simpa only [Args.append,applyAux,ht,if_true] using hh
      · simp [applyAux,ht] at hfirst
    | head g bs =>
      cases hc : consumeTypes g.result (.cons a rest) with
      | none => simp [applyAux,hc] at hfirst
      | some υ =>
        simp only [applyAux,hc,Option.map_some,Option.some.injEq] at hfirst
        subst r
        obtain ⟨ξ,hconsume,hout⟩ := markedAfter g g.result υ (substituteArgs values 0 bs) .nil (.cons a rest) second w hc hsecond
        simp only [Args.append] at hconsume hout
        apply Or.inl
        simp only [Args.append,applyAux,hconsume,Option.map_some]
        exact congrArg some hout.symm
    | marked g σ bs es =>
      cases hc : consumeTypes σ (.cons a rest) with
      | none => simp [applyAux,hc] at hfirst
      | some υ =>
        simp only [applyAux,hc,Option.map_some,Option.some.injEq] at hfirst
        subst r
        obtain ⟨ξ,hconsume,hout⟩ := markedAfter g σ υ (substituteArgs values 0 bs) (substituteArgs values 0 es) (.cons a rest) second w hc hsecond
        simp only [Args.append] at hconsume hout
        apply Or.inl
        simp only [Args.append,applyAux,hconsume,Option.map_some]
        exact congrArg some hout.symm
termination_by sizeOf first

theorem auxiliaryTwoStage : PrefixEscapeSupportTargets.AuxiliaryTwoStage := staged
end LogicLineages.PersistentMarking.PrefixTwoStageProof
