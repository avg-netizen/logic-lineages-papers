module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationGuardProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationPathProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationHeadProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowPreservationGuardProof
open NumberedWindowApplicationDomainProof (annotation rootInWindow subtypeSelf arrowLeft arrowRight)
open NumberedWindowNumberedDomainProof (ArgsGuard)
open NumberedWindowApplicationTargets (ArgsWindow)
open Spine (ArrowPrefix)

private theorem get {S K C qs q} (ht : ExtrasTyped C qs) (hg : ArgsGuard S K qs)
    (i : Nat) (h : qs.get i = some q) : InWindow S K C q.type q := by
  cases qs with
  | nil => cases h
  | cons a tail =>
    have gp := consParts hg
    cases ht with
    | cons ha htail =>
      cases i with
      | zero =>
        have e : a = q := Option.some.inj h
        subst q
        rw [annotation ha]
        exact ⟨ha,gp.1⟩
      | succ i => exact get htail gp.2 i h
termination_by i

theorem copies {S K C f τ n bs es} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C τ (.numbered f τ n bs es)) (k : Nat) (ds : List Ty)
    (hds : ∀ t ∈ ds, t ∈ K) : ArgsWindow S K C ds (ownerCopies f k bs es ds) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih =>
    obtain ⟨hb,he,hf,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts h
    exact .cons (NumberedWindowNumberedDomainProof.numbered hb he hf
      (hk _ (hds d List.mem_cons_self)) hbs hes)
      (ih fun x hx => hds x (List.mem_cons_of_mem _ hx))

private theorem copyParts {S K C ds qs}
    (h : ArgsWindow S K C ds qs) : BaseTyped C qs ds ∧ ArgsGuard S K qs := by
  induction h with
  | nil => exact ⟨.nil,nilGuard⟩
  | cons h _ ih => exact ⟨.cons h.1 ih.1,consGuard h.2 ih.2⟩

private theorem domainMembers {K} (hk : DecisionSourceUniverse.Closed K)
    (ds : List Ty) (τ : Ty) (h : ArrowPrefix ds τ ∈ K) : ∀ t ∈ ds, t ∈ K := by
  induction ds with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons d ds ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact arrowLeft hk h _ (subtypeSelf _)
    · exact ih (arrowRight hk h _ (subtypeSelf _)) t ht

theorem select {S K C f τ k bs es i q ds r} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C τ (.numbered f τ (k+1) bs es))
    (hget : bs.get i = some q ∨ es.get i = some q)
    (harrow : q.type = ArrowPrefix ds τ)
    (happ : applications q (ownerCopies f k bs es ds) = some r) :
    InWindow S K C τ r := by
  obtain ⟨hb,he,_,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts h
  have hq : InWindow S K C q.type q :=
    hget.elim (get (toExtras hb) hbs i) (get he hes i)
  rw [harrow] at hq
  have ho := copies hk h k ds (domainMembers hk ds τ (rootInWindow hq))
  obtain ⟨out,hor,hw⟩ := NumberedWindowApplicationPathProof.applicationsWindow S K C ds τ q _ hk hq ho
  have e : out = r := Option.some.inj (hor.symm.trans happ)
  exact e ▸ hw

theorem copy {S K C f g k bs es} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C g.result (.numbered f g.result (k+1) bs es))
    (hg : HeadInWindow S K g) :
    InWindow S K C g.result (.ordinary g (ownerCopies f k bs es g.arguments)) := by
  have hds : ∀ d ∈ g.arguments, d ∈ K := by
    intro d hd
    apply hg.2 d
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨d,hd,subtypeSelf d⟩)
  obtain ⟨ht,hw⟩ := copyParts (copies hk h k g.arguments hds)
  exact ordinary ht hg hw

end LogicLineages.PersistentMarking.NumberedWindowPreservationHeadProof
