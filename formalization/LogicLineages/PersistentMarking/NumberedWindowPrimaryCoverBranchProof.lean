import LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSimpleProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverBranchProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryCoverLayerProof
open NumberedWindowPrimaryCoverSimpleProof
open NumberedWindowPreservationGuardProof (TermGuard)
open NumberedWindowNumberedDomainProof (ArgsGuard)
open NumberedWindowApplicationDomainProof (subtypeSelf)

theorem numberedCase {S K m n f τ k bs es}
    (ib : ArgsAt S K m n bs) (ie : ArgsAt S K m n es) :
    TermAt S K m (n+1) (.numbered f τ k bs es) := by
  intro h hm hn
  have hf := admittedMem (h.2 f List.mem_cons_self)
  have hτ := h.1 τ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (subtypeSelf τ))))
  have hb : ArgsGuard S K bs :=
    ⟨fun t ht => h.1 t (List.mem_append_left _ (List.mem_append_right _ ht)),
      fun g hg => h.2 g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))⟩
  have he : ArgsGuard S K es :=
    ⟨fun t ht => h.1 t (List.mem_append_right _ ht),
      fun g hg => h.2 g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))⟩
  simp only [termBounds] at hm hn
  have hNum : max (argsBounds bs).numeral (argsBounds es).numeral ≤ m :=
    Nat.le_trans (Nat.le_max_right k _) hm
  exact numberedMem hf hτ (Nat.le_trans (Nat.le_max_left _ _) hm)
    (ib hb (Nat.le_trans (Nat.le_max_left _ _) hNum) (by omega))
    (ie he (Nat.le_trans (Nat.le_max_right _ _) hNum) (by omega))

theorem auxCase {S K m n σ τ Q A} (iq : TermAt S K m n Q) (ia : TermAt S K m n A) :
    TermAt S K m (n+1) (.auxApp σ τ Q A) := by
  intro h hm hn
  have hσ := h.1 σ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (subtypeSelf σ))))
  have hτ := h.1 τ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (subtypeSelf τ))))
  have hq : TermGuard S K Q :=
    ⟨fun t ht => h.1 t (List.mem_append_left _ (List.mem_append_right _ ht)),
      fun f hf => h.2 f (List.mem_append_left _ hf)⟩
  have ha : TermGuard S K A :=
    ⟨fun t ht => h.1 t (List.mem_append_right _ ht),
      fun f hf => h.2 f (List.mem_append_right _ hf)⟩
  simp only [termBounds] at hm hn
  exact auxMem hσ hτ
    (iq hq (Nat.le_trans (Nat.le_max_left _ _) hm) (by omega))
    (ia ha (Nat.le_trans (Nat.le_max_right _ _) hm) (by omega))

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverBranchProof
