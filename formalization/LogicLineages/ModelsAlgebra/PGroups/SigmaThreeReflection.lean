module
public import LogicLineages.ModelsAlgebra.PGroups.SigmaThreeReflectionTargets
public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun j => f (append a c j)) = append (fun j => f (a j)) (fun j => f (c j)) := by
  funext j
  induction j using Fin.addCases <;> simp [append]

theorem pi_two_parameterized_reflection : Targets.groupPiTwoParameterizedReflection := by
  intro G H _ _ i _ hfix n a φ hφ ht
  generalize hα : (2 : Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => simp at hα
  | pi positive s m matrix β lower rank =>
    intro b d
    obtain ⟨f,hf,hfd⟩ := hfix (n+m b) (append a d)
    have below : β b < 2 := by simpa only [← hα] using lower b
    have h := embedding_low_sigma_ascent (β b) below G H f hf (n+m b)
      (fun j => i (append a d j)) (matrix b) (rank b)
      (by simpa only [hom_append] using ht b (fun j => i (d j)))
    have he : (fun j => f (i (append a d j))) = append a d := funext hfd
    simpa only [he] using h

theorem sigma_three_stage_reflection : Targets.groupSigmaThreeStageReflection := by
  intro G _ S hmono hcover hfix φ hφ ht
  generalize hα : (3 : Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => simp at hα
  | sigma positive s m matrix β lower rank =>
    obtain ⟨b,d,hd⟩ := ht
    obtain ⟨k,hk⟩ := increasing_tuple_containment G S hmono hcover (m b) d
    let e : Fin (m b) → S k := fun j => ⟨d j,hk j⟩
    refine ⟨k,b,e,?_⟩
    have he : (fun j => (S k).subtype (append (Fin.elim0 : Fin 0 → S k) e j)) =
        append (Fin.elim0 : Fin 0 → G) d := by
      rw [hom_append]
      congr 1
      funext j
      exact Fin.elim0 j
    have hthree : (2 : Ordinal.{0}) + 1 = 3 := by simpa only [show (2+1 : ℕ) = 3 from rfl, Nat.cast_ofNat, Nat.cast_one] using (Nat.cast_add (R := Ordinal) 2 1).symm
    have below : β b < (2 : Ordinal.{0})+1 := by simpa only [← hα, hthree] using lower b
    have hle : β b ≤ 2 := Order.lt_add_one_iff.mp below
    by_cases hb : β b = 2
    · apply pi_two_parameterized_reflection G (S k) (S k).subtype Subtype.val_injective (hfix k)
        (0+m b) (append Fin.elim0 e) (matrix b) (hb ▸ rank b)
      simpa only [he] using hd
    · apply embedding_low_pi_descent (β b) (lt_of_le_of_ne hle hb) (S k) G
        (S k).subtype Subtype.val_injective (0+m b) (append Fin.elim0 e) (matrix b) (rank b)
      simpa only [he] using hd

theorem chain_no_sigma_three_scott : Targets.groupChainNoSigmaThreeScott := by
  intro G _ _ S hmono hcover hfix hnon φ hφ hs
  obtain ⟨k,hk⟩ := sigma_three_stage_reflection G S hmono hcover hfix φ hφ hs.1
  letI : Countable (S k) := Subtype.val_injective.countable
  exact hnon k (hs.2 (S k) hk)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
