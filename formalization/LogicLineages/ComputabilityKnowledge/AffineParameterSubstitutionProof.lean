module

public import LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterSubstitution
public import LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof

@[expose] public section

/-! External affine compiler supplier after independently compiled target
freeze. This pays literal positive-source substitution, not the separate
original WW vector/admissibility/norm bridge of the full corollary. -/
namespace LogicLineages.ComputabilityKnowledge.AffineParameterSubstitutionProof

open PositiveExpression CircuitReduction FiniteComparisonEnumeration
open ExponentialNormalizerProgram ExponentialNormalizerProgramSemantics
open AffineParameterSubstitution

private theorem copies_depth {ι : Type} (k : Nat) (e : Expr ι) : (copies k e).depth = e.depth := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copies, Expr.depth, ih]

private theorem copies_eval {ι : Type} (k : Nat) (e : Expr ι) (ρ : ι → PosNat) :
    (copies k e).eval ρ = (k + 1) * e.eval ρ := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp only [copies, eval_add, ih, Nat.add_mul, Nat.one_mul]; omega

private theorem copies_code (k : Nat) (e : Expr (Fin 1)) :
    copiesCode k (encodeExpr (e.rename Fin.val)) = encodeExpr ((copies k e).rename Fin.val) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copiesCode, copies, Expr.rename, encodeExpr, ih]

theorem coordinateSyntax : Comparators.AffineParameterSubstitution.CoordinateSyntax := by
  intro a b
  have hd : (coordinateExpr a b).depth = 0 := by
    unfold coordinateExpr
    split_ifs <;> simp [copies_depth, Expr.depth]
  have hc : coordinateCode a b = encodeExpr ((coordinateExpr a b).rename Fin.val) := by
    have hzero := copies_code (b - 1) (Expr.one : Expr (Fin 1))
    have hvar := copies_code (a - 1) (Expr.var 0 : Expr (Fin 1))
    simp only [Expr.rename, encodeExpr, Fin.val_zero] at hzero hvar
    by_cases ha : a = 0
    · simpa only [coordinateCode, coordinateExpr, ha, ↓reduceIte] using hzero
    · by_cases hb : b = 0
      · simpa only [coordinateCode, coordinateExpr, ha, hb, ↓reduceIte] using hvar
      · simp only [coordinateCode, coordinateExpr, ha, hb, ↓reduceIte, Expr.rename, encodeExpr]
        rw [hvar, hzero]
  refine ⟨hd, hc, ?_⟩
  intro n hab
  by_cases ha : a = 0
  · subst a
    have hb : 1 ≤ b := by omega
    simp [coordinateExpr, copies_eval, Nat.sub_add_cancel hb]
  · by_cases hb : b = 0
    · subst b
      have ha1 : 1 ≤ a := by omega
      simp [coordinateExpr, ha, copies_eval, Nat.sub_add_cancel ha1]
    · have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      simp [coordinateExpr, ha, hb, copies_eval, Nat.sub_add_cancel ha1, Nat.sub_add_cancel hb1]

theorem positiveCoordinates : Comparators.AffineParameterSubstitution.PositiveCoordinates := by
  intro d as bs h n i
  have hp := h.2.2 i
  have hn : 1 ≤ (n : Nat) := n.property
  have hm := Nat.mul_le_mul_left (as.getD i.val 0) hn
  simp only [Nat.mul_one] at hm
  omega

theorem literalSubstitution : Comparators.AffineParameterSubstitution.LiteralSubstitution := by
  intro d as bs e h
  induction e with
  | one => exact ⟨rfl, fun _ _ _ => rfl⟩
  | var i =>
      refine ⟨(coordinateSyntax _ _).1, ?_⟩
      intro n ρ hρ
      exact (coordinateSyntax _ _).2.2 n (h.2.2 i) |>.trans (hρ i).symm
  | add a b ha hb =>
      refine ⟨by simp [substitute, Expr.depth, ha.1, hb.1], ?_⟩
      intro n ρ hρ
      simp [substitute, ha.2 n ρ hρ, hb.2 n ρ hρ]
  | emul a b ha hb =>
      refine ⟨by simp [substitute, Expr.depth, ha.1, hb.1], ?_⟩
      intro n ρ hρ
      simp [substitute, ha.2 n ρ hρ, hb.2 n ρ hρ]

private theorem fold_guard (as bs : List Nat) (xs : List Nat) :
    xs.foldr (fun i acc => if 0 < as.getD i 0 + bs.getD i 0 then acc else false) true = true ↔
      ∀ i ∈ xs, 0 < as.getD i 0 + bs.getD i 0 := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      rw [List.foldr_cons]
      by_cases h : 0 < as.getD i 0 + bs.getD i 0
      · rw [if_pos h, ih]
        constructor
        · intro hall j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact h
          · exact hall j hj
        · intro hall j hj
          exact hall j (List.mem_cons_of_mem i hj)
      · rw [if_neg h]
        constructor
        · intro hh; cases hh
        · intro hall; exact False.elim (h (hall i List.mem_cons_self))

theorem coefficientDomain : Comparators.AffineParameterSubstitution.CoefficientDomain := by
  intro d as bs
  by_cases ha : as.length = d
  · by_cases hb : bs.length = d
    · simp only [coefficientsOK, ha, hb, ↓reduceIte, fold_guard, Admissible, true_and]
      constructor
      · intro h i
        exact h i.val (List.mem_range.mpr i.isLt)
      · intro h i hi
        exact h ⟨i, List.mem_range.mp hi⟩
    · simp [coefficientsOK, Admissible, ha, hb]
  · simp [coefficientsOK, Admissible, ha]

private theorem interpret_substitution (d : Nat) (as bs : List Nat) (e : Expr (Fin d)) :
    interpret [0] (fun i => coordinateCode (as.getD i 0) (bs.getD i 0))
      (fun a b => 2 :: (a ++ b)) (fun a b => 3 :: (a ++ b)) (e.rename Fin.val) =
        encodeExpr ((substitute as bs e).rename Fin.val) := by
  induction e with
  | one => rfl
  | var i => exact (coordinateSyntax _ _).2.1
  | add a b ha hb => simp only [interpret, substitute, Expr.rename, encodeExpr, ha, hb]
  | emul a b ha hb => simp only [interpret, substitute, Expr.rename, encodeExpr, ha, hb]

theorem literalCompiler : Comparators.AffineParameterSubstitution.LiteralCompiler := by
  intro d as bs e h
  have hc := (coefficientDomain d as bs).mpr h
  have hd := (FiniteComparisonEnumerationProof.expressionDecoderExact d _ (e.rename Fin.val)).mpr
    ⟨rfl, finite_rename_bounded d e⟩
  simp only [AffineParameterSubstitution.compileCode, hc, ↓reduceIte, processCode_sim, hd, Option.map_some,
    interpret_substitution]

theorem exactRawDomain : Comparators.AffineParameterSubstitution.ExactRawDomain := by
  intro d as bs raw
  cases hc : coefficientsOK d as bs <;> simp [AffineParameterSubstitution.compileCode, hc, processCode_sim]

theorem outputSourceSyntax : Comparators.AffineParameterSubstitution.OutputSourceSyntax := by
  intro d as bs raw out hout
  have hd := exactRawDomain d as bs raw
  rw [hout] at hd
  have hh : coefficientsOK d as bs = true ∧ (decodeExpr d raw).isSome = true := by
    simpa using hd.symm
  obtain ⟨e, rfl⟩ := (ExponentialIdentityProof.rawInputCoverage d raw).mp hh.2
  have hc := literalCompiler d as bs e ((coefficientDomain d as bs).mp hh.1)
  exact ⟨substitute as bs e, Option.some.inj (hout.symm.trans hc)⟩

theorem pr_copiesCode : Primrec (fun p : Nat × List Nat => copiesCode p.1 p.2) := by
  have hstep : Primrec₂ (fun (p : Nat × List Nat) (q : Nat × List Nat) => 2 :: (p.2 ++ q.2)) :=
    (Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.nat_rec' Primrec.fst Primrec.snd hstep).of_eq (by
    rintro ⟨k, raw⟩
    induction k with
    | zero => rfl
    | succ k ih => simpa [copiesCode] using congrArg (fun xs => 2 :: (raw ++ xs)) ih)

theorem pr_coordinateCode : Primrec (fun p : Nat × Nat => coordinateCode p.1 p.2) := by
  have ha : Primrec (fun p : Nat × Nat => copiesCode (p.1 - 1) [1, 0]) :=
    pr_copiesCode.comp ((Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).pair (Primrec.const [1, 0]))
  have hb : Primrec (fun p : Nat × Nat => copiesCode (p.2 - 1) [0]) :=
    pr_copiesCode.comp ((Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)).pair (Primrec.const [0]))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) hb
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) ha
      (Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_append.comp ha hb)))

theorem pr_coefficientsOK : Primrec (fun p : Nat × List Nat × List Nat => coefficientsOK p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × List Nat × List Nat => p.1) := Primrec.fst
  have ha : Primrec (fun p : Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (p : Nat × List Nat × List Nat) (q : Nat × Bool) =>
      if 0 < p.2.1.getD q.1 0 + p.2.2.getD q.1 0 then q.2 else false) := by
    have hx : Primrec (fun q : (Nat × List Nat × List Nat) × (Nat × Bool) => q.1.2.1.getD q.2.1 0) :=
      (Primrec.list_getD 0).comp (ha.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    have hy : Primrec (fun q : (Nat × List Nat × List Nat) × (Nat × Bool) => q.1.2.2.getD q.2.1 0) :=
      (Primrec.list_getD 0).comp (hb.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    exact (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.nat_add.comp hx hy))
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)).to₂
  have hfold := Primrec.list_foldr (Primrec.list_range.comp hd) (Primrec.const true) hstep
  exact Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp ha) hd)
    (Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hb) hd) hfold (Primrec.const false))
    (Primrec.const false)

private theorem pr_process : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat =>
    processCode [0] (fun i => coordinateCode (p.1.2.1.getD i 0) (p.1.2.2.getD i 0))
      (fun a b => 2 :: (a ++ b)) (fun a b => 3 :: (a ++ b)) p.1.1 p.2) := by
  have hvar : Primrec (fun p : (Nat × List Nat × List Nat) × Nat =>
      coordinateCode (p.1.2.1.getD p.2 0) (p.1.2.2.getD p.2 0)) := by
    have ha : Primrec (fun p : (Nat × List Nat × List Nat) × Nat => p.1.2.1.getD p.2 0) :=
      (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have hb : Primrec (fun p : (Nat × List Nat × List Nat) × Nat => p.1.2.2.getD p.2 0) :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact pr_coordinateCode.comp (ha.pair hb)
  have hadd : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat × List Nat => 2 :: (p.2.1 ++ p.2.2)) :=
    Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_append.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hexp : Primrec (fun p : (Nat × List Nat × List Nat) × List Nat × List Nat => 3 :: (p.2.1 ++ p.2.2)) :=
    Primrec.list_cons.comp (Primrec.const 3) (Primrec.list_append.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact ExponentialNormalizerProgramEffectivity.pr_processCode
    (fun p : Nat × List Nat × List Nat => p.1) (fun _ => [0])
    (fun p i => coordinateCode (p.2.1.getD i 0) (p.2.2.getD i 0))
    (fun _ a b => 2 :: (a ++ b)) (fun _ a b => 3 :: (a ++ b))
    Primrec.fst (Primrec.const [0]) hvar hadd hexp

theorem pr_compileCode : Primrec (fun p : Nat × List Nat × List Nat × List Nat =>
    compileCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hparams : Primrec (fun p : Nat × List Nat × List Nat × List Nat => (p.1, p.2.1, p.2.2.1)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hraw : Primrec (fun p : Nat × List Nat × List Nat × List Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp := pr_process.comp (hparams.pair hraw)
  have hc := pr_coefficientsOK.comp hparams
  exact (Primrec.ite (Primrec.eq.comp hc (Primrec.const true)) hp (Primrec.const none)).of_eq (fun _ => rfl)

theorem actualUniformPrograms : Comparators.AffineParameterSubstitution.ActualUniformPrograms :=
  ⟨pr_copiesCode, pr_coordinateCode, pr_coefficientsOK, pr_compileCode⟩

theorem affineParameterSubstitution : Comparators.AffineParameterSubstitution.Target :=
  ⟨coordinateSyntax, positiveCoordinates, literalSubstitution, coefficientDomain,
    literalCompiler, exactRawDomain, outputSourceSyntax, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.AffineParameterSubstitutionProof
