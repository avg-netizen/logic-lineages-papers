module
public import LogicLineages.PermittedControl.GapInputTargets
public import LogicLineages.PermittedControl.CountLagProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem selected_laws (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) : Targets.ControlLaws f B := by
  rcases hf with ⟨rfl,rfl⟩ | ⟨b,rfl,rfl⟩
  · exact factorial_control_laws
  · exact near_control_laws b

 theorem selected_strict_expand (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (n : Nat) : n < f n := by
  have h := (selected_threshold_admissible f B hf).2 n
  have hg := G_large n
  omega

 theorem selected_margin (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (S n : Nat) (hn : S ≤ n) : n+S ≤ f n := by
  have h := (selected_threshold_admissible f B hf).2 n
  have hg := G_large n
  omega

 theorem selected_adjacent_margin (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (S n : Nat) (hn : S ≤ n) : f n+S ≤ f (n+1) := by
  have hlarge := selected_strict_expand f B hf n
  have hpow := twice_self_le_two_pow (n := f n) (by omega)
  have hpow' := (Nat.lt_two_pow_self (n := 2^(f n))).le
  have hg := (selected_laws f B hf).2.2.2.1 n
  omega

 theorem selected_input_margin (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (S n m : Nat) (hn : S ≤ n) (hnm : n < m) : f n+S ≤ f m :=
  (selected_adjacent_margin f B hf S n hn).trans
    ((selected_threshold_admissible f B hf).1.monotone (by omega))

 theorem selected_iterate_strict (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (t : Nat) : StrictMono (fun i : Nat => f^[i] t) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [Function.iterate_succ_apply']
  exact selected_strict_expand f B hf _

 theorem gap_initial_limit (f : Nat → Nat) (lam mu : Ordinal.{0}) (t : Nat)
    (hl : Order.IsSuccLimit lam) (hml : mu < lam) :
    actualLimitPart (relativeState f lam mu t 0) = lam-mu := by
  have hd := Ordinal.isSuccLimit_sub hl.isSuccPrelimit hml
  have heq : mu+(lam-mu) = lam := Ordinal.add_sub_cancel_of_le hml.le
  simp only [relativeState, Function.iterate_zero_apply, countInitial]
  rw [← heq, add_assoc, Ordinal.add_sub_cancel, Ordinal.add_sub_cancel]
  exact limitPart_tail _ hd _

 theorem gap_norm_le (lam mu : Ordinal.{0}) (ha : lam < epsilonZero) (hml : mu ≤ lam) :
    actualOrdinalNorm (lam-mu) ≤ actualOrdinalNorm lam := by
  have hd : lam-mu < epsilonZero := (Ordinal.sub_le_self _ _).trans_lt ha
  have hn := (relativeNorm mu (lam-mu) (hml.trans_lt ha) hd).1
  rw [Ordinal.add_sub_cancel_of_le hml] at hn
  omega

 theorem reserve_norm_le (delta : Ordinal.{0}) (hd : delta < epsilonZero) (r : Nat) :
    delta+Ordinal.omega0*(r : Ordinal) < epsilonZero ∧
    actualOrdinalNorm (delta+Ordinal.omega0*(r : Ordinal)) ≤ actualOrdinalNorm delta+2*r := by
  have hw : Ordinal.omega0*(r : Ordinal) < epsilonZero := by simpa using finiteCoefficient_below r 0
  have hn := relativeNorm delta (Ordinal.omega0*(r : Ordinal)) hd hw
  have hnorm : actualOrdinalNorm (Ordinal.omega0*(r : Ordinal)) = 2*r := by
    simpa using actualFiniteHeadNorm r 0
  refine ⟨epsilonZero_add_principal hd hw, ?_⟩
  rw [hn.1, hnorm]
  have hc := hn.2.2
  omega

 theorem reserve_limit (delta : Ordinal.{0}) (hd : Order.IsSuccLimit delta) (r : Nat) :
    Order.IsSuccLimit (delta+Ordinal.omega0*(r : Ordinal)) := by
  cases r with
  | zero => simpa using hd
  | succ r =>
    exact Ordinal.isSuccLimit_add delta
      (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast Nat.succ_pos r))

 theorem gap_tail_bounds (lam mu lam' mu' : Ordinal.{0}) (k : Nat) :
    max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ gapInputTail lam mu lam' mu' k ∧
    max 2 (max (actualOrdinalNorm lam') (actualOrdinalNorm mu')) ≤ gapInputTail lam mu lam' mu' k ∧
    gapProfileBound mu mu' ≤ gapInputTail lam mu lam' mu' k ∧
    actualOrdinalNorm lam'+2*k+actualOrdinalNorm mu ≤ gapInputTail lam mu lam' mu' k := by
  unfold gapInputTail gapProfileBound
  omega

 theorem gapInputTailEffective : Targets.GapInputTailEffective := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have h1 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.1) := Primrec.fst
  have h2 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.1) := Primrec.fst.comp Primrec.snd
  have h3 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h4 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h5 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he : Primrec encodedGapInputTail :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2) (hn.comp h1)) (hn.comp h3))
      (Primrec.nat_max.comp (Primrec.const 1) (Primrec.nat_max.comp (hn.comp h2) (hn.comp h4))))
      (Primrec.nat_mul.comp (Primrec.const 2) h5)
  refine ⟨he.to_comp, ?_⟩
  intro lam mu lam' mu' k
  simp only [encodedGapInputTail, gapInputTail, gapProfileBound]
  rw [rawNormCodeCorrect lam.1, rawNormCodeCorrect mu.1, rawNormCodeCorrect lam'.1,
    rawNormCodeCorrect mu'.1, actualOrdinalNorm_notationCorrespondence lam,
    actualOrdinalNorm_notationCorrespondence mu, actualOrdinalNorm_notationCorrespondence lam',
    actualOrdinalNorm_notationCorrespondence mu']

end LogicLineages.PermittedControl
