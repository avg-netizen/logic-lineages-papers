module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRefinementProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedListProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination

theorem permuteRight {alpha beta : Type} (R : alpha → beta → Prop) {ss ts : List beta} (hp : ss.Perm ts) :
    ∀ qs : List alpha,List.Forall₂ R qs ss → ∃ rs : List alpha,qs.Perm rs ∧ List.Forall₂ R rs ts := by
  induction hp with
  | nil =>
    intro qs hq
    cases hq
    exact ⟨[],.nil,.nil⟩
  | cons s hp ih =>
    intro qs hq
    cases hq with
    | @cons q _ qs _ hhead htail =>
      obtain ⟨rs,hperm,hrel⟩ := ih qs htail
      exact ⟨q::rs,hperm.cons q,.cons hhead hrel⟩
  | swap a b rest =>
    intro qs hq
    cases hq with
    | @cons qb _ qtail _ hqb htail =>
      cases htail with
      | @cons qa _ qrest _ hqa hrest =>
        exact ⟨qa::qb::qrest,.swap qa qb qrest,.cons hqa (.cons hqb hrest)⟩
  | trans hp hq ihp ihq =>
    intro qs hrel
    obtain ⟨rs,hpr,hr⟩ := ihp qs hrel
    obtain ⟨us,hru,hu⟩ := ihq rs hr
    exact ⟨us,hpr.trans hru,hu⟩

theorem splitRight {alpha beta : Type} (R : alpha → beta → Prop) (left right : List beta) :
    ∀ qs : List alpha,List.Forall₂ R qs (left++right) →
      ∃ l r : List alpha,qs=l++r ∧ List.Forall₂ R l left ∧ List.Forall₂ R r right := by
  induction left with
  | nil => intro qs h; exact ⟨[],qs,rfl,.nil,h⟩
  | cons s left ih =>
    intro qs h
    cases h with
    | @cons q _ rest _ hq hr =>
      obtain ⟨l,r,he,hl,hr'⟩ := ih rest hr
      exact ⟨q::l,r,by simp only [List.cons_append,he],.cons hq hl,hr'⟩

theorem refinePartition {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ss kept removed qs : List (Packed Symbol arity Gamma)) (hp : ss.Perm (kept++removed))
    (hq : List.Forall₂ (Refines Symbol arity Gamma) qs ss) :
    ∃ qkept qremoved : List (Packed Symbol arity Gamma),qs.Perm (qkept++qremoved) ∧
      List.Forall₂ (Refines Symbol arity Gamma) qkept kept ∧ List.Forall₂ (Refines Symbol arity Gamma) qremoved removed := by
  obtain ⟨rs,hperm,hrel⟩ := permuteRight (Refines Symbol arity Gamma) hp qs hq
  obtain ⟨l,r,he,hl,hr⟩ := splitRight (Refines Symbol arity Gamma) kept removed rs hrel
  exact ⟨l,r,he ▸ hperm,hl,hr⟩

theorem matchNil {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) : MatchMeaning above ([] : List (Packed Symbol arity Gamma)) [] := by
  intro qs hq ht
  cases hq
  exact .nil

theorem matchCons {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) (ss ts : List (Packed Symbol arity Gamma))
    (hq : WeakMeaning above s t) (hr : MatchMeaning above ss ts) : MatchMeaning above (s::ss) (t::ts) := by
  intro qs hRef ht
  cases hRef with
  | @cons q _ rest _ hs hrest =>
    exact .cons q t rest ts (hq q hs (ht t (List.mem_cons_self ..)))
      (hr rest hrest (fun p hp => ht p (List.mem_cons_of_mem _ hp)))

theorem replacementNil {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (removed : List (Packed Symbol arity Gamma)) : ReplacementMeaning above removed [] := by
  intro qs hRef ht
  exact .nil qs

theorem replacementCons {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (removed : List (Packed Symbol arity Gamma))
    (s t : Packed Symbol arity Gamma) (rest : List (Packed Symbol arity Gamma))
    (hm : s∈removed) (hs : StrictMeaning above s t) (hr : ReplacementMeaning above removed rest) :
    ReplacementMeaning above removed (t::rest) := by
  intro qs hRef ht
  obtain ⟨q,hq,hqs⟩ := SourceExtendedRefinementProof.memberRight hRef s hm
  exact .cons qs q t rest hq (hs q hqs (ht t (List.mem_cons_self ..)))
    (hr qs hRef (fun p hp => ht p (List.mem_cons_of_mem _ hp)))

theorem multiset {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts kept retained removed inserted : List (Packed Symbol arity Gamma))
    (hs : ss.Perm (kept++removed)) (ht : ts.Perm (retained++inserted)) (hn : removed≠[])
    (hw : MatchMeaning above kept retained) (hr : ReplacementMeaning above removed inserted) : MultiMeaning above ss ts := by
  intro qs hRef htOrd
  obtain ⟨qkept,qremoved,hperm,hkept,hremoved⟩ := refinePartition ss kept removed qs hs hRef
  apply StrictMultiset.replace qs ts qkept retained qremoved inserted hperm ht
  · intro hz
    rw [hz] at hremoved
    cases hremoved
    exact hn rfl
  · exact hw qkept hkept (fun p hp => htOrd p (ht.symm.subset (List.mem_append_left _ hp)))
  · exact hr qremoved hremoved (fun p hp => htOrd p (ht.symm.subset (List.mem_append_right _ hp)))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedListProof
