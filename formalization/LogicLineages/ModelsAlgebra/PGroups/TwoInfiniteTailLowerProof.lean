module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTailLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTerminalDeletionProof
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem two_infinite_tail_no_difference : Targets.twoInfiniteTailNoDifference := by
  classical
  intro G _ _ p _ hG rG γ N a b hab hN ha hb d hd hs
  have hScott := raw_difference_scott_restriction G d hs
  have hσ := hd.1
  have htruth := hScott.1.1
  generalize hform : d.sigmaPart=φ at hσ htruth
  generalize hlevel : 2*γ+2=α at hσ
  cases hσ with
  | qf side q => exact ((by positivity : (2*γ+2:Ordinal) ≠ 0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    obtain ⟨i,c,hc⟩ := htruth
    obtain ⟨T,M,_,_,hne,hodd,heven⟩ := two_infinite_terminal_deletion G p hG rG γ N a b hab hN ha hb
      (0+m i) (append Fin.elim0 c)
    let Q := G ⧸ T
    let q := QuotientAddGroup.mk' T
    letI : Countable Q := (QuotientAddGroup.mk'_surjective T).countable
    have hβ : β i ≤ 2*γ+1 := by
      apply Order.le_of_lt_succ
      simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using lower i
    have hbf := back_forth_monotone (2*γ+1) (β i) hβ G Q (0+m i) _ _ hodd
    have hmat := (truth_transfer (β i) G Q (0+m i) _ _ hbf).1 (matrix i) (rank i) hc
    have hnil : (fun i : Fin 0 => q (Fin.elim0 i)) = Fin.elim0 := by funext i; exact Fin.elim0 i
    change (matrix i).Realize (fun j => q (append Fin.elim0 c j)) at hmat
    rw [hom_append,hnil] at hmat
    have hsQ : d.sigmaPart.Realize (Fin.elim0 : Fin 0 → Q) := by
      rw [hform]
      exact ⟨i,fun j => q (c j),hmat⟩
    have hpQ := (truth_transfer (2*γ+2) G Q 0 Fin.elim0 Fin.elim0 heven).1 d.piPart hd.2 hScott.1.2
    exact hne (hScott.2 Q ⟨hsQ,hpQ⟩)
end LogicLineages.ModelsAlgebra.PGroups
