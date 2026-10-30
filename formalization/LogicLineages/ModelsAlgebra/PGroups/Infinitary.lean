module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryTargets
public import LogicLineages.ModelsAlgebra.PGroups.BackForth

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem qf_truth_agreement : Targets.groupQFTruthAgreement.{u} := by
  intro A B _ _ n a b hab q
  induction q with
  | equal s t => exact hab s t
  | falsum => exact Iff.rfl
  | neg q ih => exact not_congr ih
  | and p q ihp ihq => exact and_congr ihp ihq

private theorem append_nil {G : Type u} {n : ℕ} (a : Fin n → G) (c : Fin 0 → G) :
    append a c = a := by
  funext i
  simpa [append] using (Fin.addCases_left (m := n) (n := 0) (motive := fun _ => G)
    (left := a) (right := c) i)

theorem sigma_qf_padding : Targets.groupSigmaQFPadding.{u,v} := by
  intro α hα n q
  constructor
  · exact Complexity.sigma hα {0} (fun _ => 0) (fun _ => .qf q)
      (fun _ => 0) (fun _ => bot_lt_iff_ne_bot.mpr hα) (fun _ => Complexity.qf .pi q)
  · intro G _ a
    change (∃ i : ({0} : Set ℕ), ∃ c : Fin 0 → G, q.Realize (append a c)) ↔ q.Realize a
    constructor
    · rintro ⟨i, c, hc⟩
      simpa only [append_nil] using hc
    · intro hq
      exact ⟨⟨0, by simp⟩, Fin.elim0, by simpa only [append_nil] using hq⟩

theorem pi_qf_padding : Targets.groupPiQFPadding.{u,v} := by
  intro α hα n q
  constructor
  · exact Complexity.pi hα {0} (fun _ => 0) (fun _ => .qf q)
      (fun _ => 0) (fun _ => bot_lt_iff_ne_bot.mpr hα) (fun _ => Complexity.qf .sigma q)
  · intro G _ a
    change (∀ i : ({0} : Set ℕ), ∀ c : Fin 0 → G, q.Realize (append a c)) ↔ q.Realize a
    constructor
    · intro h
      simpa only [append_nil] using h ⟨0, by simp⟩ Fin.elim0
    · intro hq i c
      simpa only [append_nil] using hq

theorem truth_transfer : Targets.groupInfinitaryTruthTransfer.{u,v} := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro A B _ _ n a b hab
    constructor
    · intro φ hφ ha
      cases hφ with
      | qf side q =>
        exact (qf_truth_agreement A B n a b ((zero_comparison A B n a b).mp hab) q).mp ha
      | pi positive s m matrix β lower rank =>
        intro i d
        obtain ⟨c, hc⟩ := (positive_comparison α positive A B n a b).mp hab
          (β i) (lower i) (m i) d
        exact (ih (β i) (lower i) B A (n + m i) (append b d) (append a c) hc).2
          (matrix i) (rank i) (ha i c)
    · intro φ hφ hb
      cases hφ with
      | qf side q =>
        exact (qf_truth_agreement A B n a b ((zero_comparison A B n a b).mp hab) q).mpr hb
      | sigma positive s m matrix β lower rank =>
        obtain ⟨i, d, hd⟩ := hb
        obtain ⟨c, hc⟩ := (positive_comparison α positive A B n a b).mp hab
          (β i) (lower i) (m i) d
        exact ⟨i, c, (ih (β i) (lower i) B A (n + m i) (append b d) (append a c) hc).1
          (matrix i) (rank i) hd⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
