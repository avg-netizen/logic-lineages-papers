module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsSupportProof
open Source Source.SourceMarkedSyntax RecursiveComparison LiteralContexts

private theorem matchWitness {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Γ : List Ty} {ss ts : List (Packed Symbol arity Γ)}
    (h : WeakMatch Symbol arity above Γ ss ts) :
    ∀ t ∈ ts, ∃ s ∈ ss, Weak Symbol arity above Γ s t := by
  induction ss generalizing ts with
  | nil => cases h; simp
  | cons a xs ih =>
      cases h with
      | cons _ b _ ys hab hrest =>
          intro t ht
          rcases List.mem_cons.mp ht with ht | ht
          · subst t; exact ⟨a,by simp,hab⟩
          · obtain ⟨s,hs,hw⟩ := ih hrest t ht
            exact ⟨s,List.mem_cons_of_mem a hs,hw⟩

theorem strictMultisetFromStrictMatch : LiteralContextsTargets.StrictMultisetFromStrictMatch := by
  intro Symbol arity above Γ ss
  induction ss with
  | nil => intro ts hm he; cases hm; simpa using he
  | cons a xs ih =>
      intro ts hm he
      cases hm with
      | cons _ b _ ys hab hrest =>
          obtain ⟨u,v,hmem,hstrict⟩ := he
          rcases List.mem_cons.mp hmem with heq | htail
          · cases heq
            exact .replace (a::xs) (b::ys) xs ys [a] [b]
              (by simpa using (List.perm_append_comm : ([a]++xs).Perm (xs++[a])))
              (by simpa using (List.perm_append_comm : ([b]++ys).Perm (ys++[b])))
              (by simp) hrest (.cons [a] a b [] (by simp) hstrict (.nil [a]))
          · have hm := ih ys hrest ⟨u,v,htail,hstrict⟩
            cases hm with
            | replace _ _ kept retained removed inserted hp hq hn hw hr =>
                exact .replace (a::xs) (b::ys) (a::kept) (b::retained) removed inserted
                  (List.Perm.cons a hp) (List.Perm.cons b hq) hn
                  (.cons a b kept retained hab hw) hr

theorem actualZeroArgumentSelect : LiteralContextsTargets.ActualZeroArgumentSelect := by
  intro Symbol arity above Γ f base types extras τ q t hmem hw
  apply Weak.select f base types extras [] q q t rfl hmem
  · exact Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Γ τ q
  · exact hw

theorem ordinaryHeadStrictCongruence : LiteralContextsTargets.OrdinaryHeadStrictCongruence := by
  intro Symbol arity above Γ f ss ts hm hs
  apply Strict.mark (.ordinary f ss) (.marked f (headResult f) ss [] .nil) (.ordinary f ts) rfl
  apply Weak.stat f f ss [] .nil ts rfl (strictMultisetFromStrictMatch Symbol arity above Γ _ _ hm hs)
  intro p hp
  obtain ⟨q,hq,hw⟩ := matchWitness hm p hp
  rcases p with ⟨τ,t⟩
  rcases q with ⟨σ,q⟩
  have he := RecursiveComparisonProof.weakTypeSoundness Symbol arity above Γ ⟨σ,q⟩ ⟨τ,t⟩ hw
  change σ=τ at he
  subst σ
  exact actualZeroArgumentSelect Symbol arity above Γ f ss [] .nil τ q t
    (List.mem_append.mpr (Or.inl hq)) hw

theorem lambdaStrictCongruence : LiteralContextsTargets.LambdaStrictCongruence := by
  intro Symbol arity above Γ σ τ s t hs
  cases hs with
  | mark s r t hm hw =>
      exact .mark (.lam s) (.lam r) (.lam t) (by simp [strictMark,hm]) (.abs r t hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsSupportProof
