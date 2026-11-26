module
public import LogicLineages.PermittedControl.CountTransferTargets
import LogicLineages.PermittedControl.CountTransferCoreProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.InverseTableProof
import LogicLineages.PermittedControl.GapInputProof
import Mathlib.Tactic.LinearCombination

public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-! Arithmetic over abstract naturals. -/

theorem transfer_sign_cases (s : Nat) (h : s ≤ 2) : s = 0 ∨ s = 1 ∨ s = 2 := by omega

theorem transfer_tail_parts (G T U C y : Nat) (h : 1+max G (max T (max U C)) ≤ y) :
    G ≤ y ∧ T ≤ y := by omega

theorem transfer_guard_parts (a k m y : Nat) (h : max 2 (max a (max k m)) ≤ y) :
    max 2 (max k m) ≤ y := by omega

/-! Iterates of a selected control from a fixed input are strictly increasing. -/

theorem selected_lt (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (n : Nat) :
    n < f n :=
  (self_lt_Phi n).trans_le ((selected_threshold_admissible f B hf).2 n)

theorem iterate_strict (f : Nat → Nat) (hlt : ∀ n, n < f n) (x : Nat) :
    StrictMono (fun i : Nat => f^[i] x) :=
  strictMono_nat_of_lt_succ (fun i => by
    show f^[i] x < f^[i+1] x
    rw [Function.iterate_succ_apply']
    exact hlt _)

theorem zeroClassExact : Targets.ZeroClassExact := by
  intro f B hf n lam mu x a b C hint hzero i k hent
  have hcore : ∀ s : Fin n, 2 * (k s : Int) =
      C + 2 * (i s : Int) + 2 * Targets.countCoreConstant (mu s) := by
    intro s
    obtain ⟨hlam,hll,hmu,hml,hlong,hx⟩ := hint s
    obtain ⟨hi,hk,hC⟩ := hent s
    obtain ⟨-,i0,k0,hi0,hk0,-,hform⟩ :=
      countCore f B hf (lam s) (mu s) (x s) hlam hll hmu hml hlong hx
    have ei := firstEntry_unique f _ _ (i s) i0 hi hi0
    have ek := firstEntry_unique f _ _ (k s) k0 hk hk0
    rw [← ei,← ek,hC] at hform
    exact hform
  have hsum : 2 * ∑ s, a s * (k s : Int) = (∑ s, a s) * C + 2 * ∑ s, a s * (i s : Int) +
      2 * ∑ s, a s * Targets.countCoreConstant (mu s) := by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have h := hcore s
    linear_combination (a s) * h
  have h2 : 2 * (b * C + ∑ s, a s * (k s : Int)) =
      2 * (∑ s, a s * (i s : Int) + ∑ s, a s * Targets.countCoreConstant (mu s)) := by
    linear_combination hsum + C * hzero
  exact mul_left_cancel₀ (by decide : (2 : Int) ≠ 0) h2

theorem equalInputMerge : Targets.EqualInputMerge := by
  intro f B hf lam mu lam' mu' x hlam hlam' hll hll' hmu hmu' hml hml' hx hx' i j hi hj heq
  obtain ⟨i0,hi0,hn⟩ := entryExistenceOrbit f B hf lam mu x hlam hll hmu hml hx
  obtain ⟨j0,hj0,hn'⟩ := entryExistenceOrbit f B hf lam' mu' x hlam' hll' hmu' hml' hx'
  have ei := firstEntry_unique f _ _ i0 i hi0 hi
  have ej := firstEntry_unique f _ _ j0 j hj0 hj
  rw [ei] at hn
  rw [ej] at hn'
  rw [hn,hn'] at heq
  exact (iterate_strict f (selected_lt f B hf) x).injective heq

theorem distinctInputGap : Targets.DistinctInputGap := by
  intro f B hf lam mu lam' mu' hlam hlam' hll hll' hmu hmu' hml hml' x y hx hy hxy i j hi hj heq
  by_contra hnot
  have hle : lam'-mu' ≤ lam-mu := not_lt.mp hnot
  obtain ⟨i0,j0,hi0,hj0,-,hlt⟩ :=
    (gapInputComparison f B hf lam mu lam' mu' hlam hlam' hll hll' hmu hmu' hml hml').2.1 hle
      y x hy hx hxy
  have ei := firstEntry_unique f _ _ i0 i hi0 hi
  have ej := firstEntry_unique f _ _ j0 j hj0 hj
  rw [ei,ej] at hlt
  exact absurd heq (Nat.ne_of_gt hlt)

theorem rankTransfer : Targets.RankTransfer := by
  intro f B hf lambda mu nu delta hll hm hn hd hml hgap x y hx hy p q hp hq heq
  obtain ⟨hmk,hklam,i,j,p',q',lo,mid,hi',hi,hxh,hh,hj,hp',hq',hpij,hcont,-,-,-,-,-,-,hrows,-⟩ :=
    actualInverseTable f B hf lambda mu nu delta hll hm hn hd hml hgap x y hx hy
  have ep := firstEntry_unique f _ _ p' p hp' hp
  have eq' := firstEntry_unique f _ _ q' q hq' hq
  rw [ep] at hpij hcont hrows
  rw [eq'] at hrows
  -- equal values force the equality certificate and `y = E_H(x)`
  have hy_eq : y = entryNormAt f (countInitial lambda.1.repr x) i := by
    rcases transfer_sign_cases _ (equalGapCertificateEffective.2.2 (rawNoteEncode mu.1)
      (rawNoteEncode nu.1) (rawNoteEncode delta.1)) with h0 | h1 | h2
    · exact absurd heq (hrows.2.2 h0).2.1
    · exact ((hrows.1 h1).2.1).mp heq
    · exact absurd heq (hrows.2.1 h2).2.1
  rw [← hy_eq] at hj hcont
  -- both remaining entries start at `y`; their norms are iterates of `f` at `y`
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hdelta := normalRepresentationSound delta
  have hk : mu.1.repr+delta.1.repr < epsilonZero := epsilonZero_add_principal hmu hdelta
  have hQ : nu.1.repr+delta.1.repr < epsilonZero := epsilonZero_add_principal hnu hdelta
  have hkl : Order.IsSuccLimit (mu.1.repr+delta.1.repr) := Ordinal.isSuccLimit_add _ hd
  have hql : Order.IsSuccLimit (nu.1.repr+delta.1.repr) := Ordinal.isSuccLimit_add _ hd
  have hnq : nu.1.repr < nu.1.repr+delta.1.repr := by
    simpa only [add_zero] using (add_lt_add_iff_left nu.1.repr).mpr hd.pos
  dsimp only [inverseTableTail] at hy
  have hparts := transfer_tail_parts _ _ _ _ y hy
  have hQtail := (gap_tail_bounds (mu.1.repr+delta.1.repr) mu.1.repr (nu.1.repr+delta.1.repr)
    nu.1.repr 0).2.1
  obtain ⟨j0,hj0,hjn⟩ := entryExistenceOrbit f B hf (mu.1.repr+delta.1.repr) mu.1.repr y hk hkl hm
    hmk (transfer_guard_parts _ _ _ y hparts.1)
  obtain ⟨q0,hq0,hqn⟩ := entryExistenceOrbit f B hf (nu.1.repr+delta.1.repr) nu.1.repr y hQ hql hn
    hnq (hQtail.trans hparts.2)
  have ej := firstEntry_unique f _ _ j0 j hj0 hj
  have eq2 := firstEntry_unique f _ _ q0 q hq0 hq
  rw [ej] at hjn
  rw [eq2] at hqn
  have hjq : f^[j] y = f^[q] y := by
    rw [← hjn,← hqn,← hcont,heq]
  have ejq : j = q := (iterate_strict f (selected_lt f B hf) y).injective hjq
  exact ⟨i,hi,hy_eq.symm,by rw [hpij,ejq]⟩

theorem fullCountTransfer : Targets.FullCountTransfer :=
  ⟨countCore,zeroClassExact,equalInputMerge,distinctInputGap,rankTransfer⟩

end LogicLineages.PermittedControl
