module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalSigmaOneTargets
public import LogicLineages.ModelsAlgebra.PGroups.Relativized
public import LogicLineages.ModelsAlgebra.PGroups.RetainedSum
public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u v

private theorem rank_zero_qf {n : ℕ} {side : Polarity} {φ : Formula n}
    (h : Complexity side (0 : Ordinal.{v}) φ) : ∃ q : QF n, φ = .qf q := by
  cases h with
  | qf side q => exact ⟨q,rfl⟩
  | sigma positive => exact (positive rfl).elim
  | pi positive => exact (positive rfl).elim

private theorem restricted_qf_hom (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (S : AddSubgroup G) (hf : Function.Injective (fun x : S => f (x:G)))
    (n : ℕ) (a : Fin n → G) (ha : ∀ j, a j ∈ S) (q : QF n) :
    q.Realize a ↔ q.Realize (fun j => f (a j)) := by
  let b : Fin n → S := fun j => ⟨a j,ha j⟩
  have hleft := qf_truth_agreement S G n b a
    (embedding_atomic_agreement S G S.subtype Subtype.val_injective n b) q
  have hright := qf_truth_agreement S H n b (fun j => f (a j))
    (embedding_atomic_agreement S H (f.comp S.subtype) hf n b) q
  exact hleft.symm.trans hright

theorem terminal_sigma_one_transfer : Targets.groupTerminalSigmaOneTransfer.{u,v} := by
  intro G _ p δ A K T hH hKT hA n a ha φ hφ ht
  obtain ⟨e,he⟩ := coherent_terminal_quotient G p δ K T hH hKT
  have hK : K ≤ (transfiniteFiltration p δ : AddSubgroup G) := by rw [hH]; exact le_sup_left
  let q := QuotientAddGroup.mk' T
  have hinj := retained_sum_quotient_injective G A K T (transfiniteFiltration p δ) hH hKT hA
  generalize hα : (1 : Ordinal.{v}) = α at hφ
  cases hφ with
  | qf side qf => simp at hα
  | sigma positive s m matrix β lower rank =>
    obtain ⟨b,c,hc⟩ := ht
    have hz : β b = 0 := Order.lt_one_iff.mp (by simpa only [← hα] using lower b)
    have hr : Complexity .pi (0 : Ordinal.{v}) (matrix b) := by simpa only [hz] using rank b
    obtain ⟨qf,hqf⟩ := rank_zero_qf hr
    let cK : Fin (m b) → K := fun j => e.symm (c j)
    let d : Fin (m b) → (transfiniteFiltration p δ : AddSubgroup G) :=
      fun j => ⟨cK j,hK (cK j).property⟩
    refine ⟨b,d,?_⟩
    rw [hqf] at hc ⊢
    let z := append a (fun j => (d j : G))
    have hzS : ∀ j, z j ∈ A ⊔ K := by
      intro j
      induction j using Fin.addCases with
      | left j => simpa [z, append] using (le_sup_left : A ≤ A ⊔ K) (ha j)
      | right j => simpa [z, append, d] using (le_sup_right : K ≤ A ⊔ K) (cK j).property
    have hd (j) : q (d j : G) = (c j : G ⧸ T) := by
      change q (e.symm (c j) : G) = (c j : G ⧸ T)
      rw [← he, e.apply_symm_apply]
    have hmap : (fun j => q (z j)) = append (fun j => q (a j)) (fun j => (c j : G ⧸ T)) := by
      funext j
      induction j using Fin.addCases with
      | left j => simp [z, append]
      | right j => simpa [z, append] using hd j
    change qf.Realize z
    apply (restricted_qf_hom G (G ⧸ T) q (A ⊔ K) hinj _ z hzS qf).mpr
    simpa only [hmap, Formula.RealizeIn, q] using hc

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
