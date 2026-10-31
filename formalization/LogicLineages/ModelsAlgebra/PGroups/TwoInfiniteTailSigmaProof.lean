module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTailSigmaTargets
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTerminalPointedProof
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem two_infinite_tail_no_sigma : Targets.twoInfiniteTailNoSigma := by
  classical
  intro G _ _ p _ hG rG γ N a b hab hN ha hb φ hc hs
  generalize hlevel : 2*γ+3 = α at hc
  cases hc with
  | qf side q => exact ((by positivity : (2*γ+3:Ordinal) ≠ 0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    obtain ⟨i,d,hd⟩ := hs.1
    obtain ⟨T,_,_,_,hne,hbf⟩ := two_infinite_terminal_pointed G p hG rG γ N a b hab hN ha hb
      (0+m i) (append Fin.elim0 d)
    let Q := G ⧸ T
    let q := QuotientAddGroup.mk' T
    letI : Countable Q := (QuotientAddGroup.mk'_surjective T).countable
    have hβ : β i ≤ 2*γ+2 := by
      apply Order.le_of_lt_succ
      simpa only [Order.succ_eq_add_one,add_assoc,show (2:Ordinal)+1=3 from by norm_num] using lower i
    have hb := back_forth_monotone (2*γ+2) (β i) hβ G Q (0+m i) _ _ hbf
    have ht := (truth_transfer (β i) G Q (0+m i) _ _ hb).1 (matrix i) (rank i) hd
    have hnil : (fun i : Fin 0 => q (Fin.elim0 i)) = Fin.elim0 := by
      funext i; exact Fin.elim0 i
    change (matrix i).Realize (fun j => q (append Fin.elim0 d j)) at ht
    rw [hom_append,hnil] at ht
    exact hne (hs.2 Q ⟨i,fun j => q (d j),ht⟩)

theorem two_infinite_tail_no_raw_sigma : Targets.twoInfiniteTailNoRawSigma := by
  intro G _ _ p _ hG rG γ N a b hab hN ha hb φ hc hs
  exact two_infinite_tail_no_sigma G p hG rG γ N a b hab hN ha hb φ hc (raw_scott_restriction G φ hs)
end LogicLineages.ModelsAlgebra.PGroups
