module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayCodeEvaluation
public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
public import LogicLineages.ComputabilityKnowledge.AffineRayCalibrationBasics

@[expose] public section

/-! External proof of literal all-raw-code evaluation, after target freeze.
Duplicate keys are handled by the proved additivity of the actual finite-map
value; no canonical-input restriction is added. -/
namespace LogicLineages.ComputabilityKnowledge.RayCodeEvaluationProof

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormProof ExponentialHereditaryCodecProof RayCodeEvaluation

theorem literalAffineEvaluation : Comparators.RayCodeEvaluation.LiteralAffineEvaluation := by
  intro d c xs
  unfold affineEval affineValue
  rw [AffineRayCalibrationBasics.fold_range_sum]
  rfl

private theorem entries_value (d h : Nat) (es : MapCode) (ρ : Fin d → Nat) :
    value (h + 1) (entriesDecode d h es) ρ =
      es.foldr (fun e acc => affineValue (coeffDecode d e.2) ρ *
        2 ^ value h (formDecode d h e.1) ρ + acc) 0 := by
  induction es with
  | nil => exact zero_value (h + 1) ρ
  | cons e es ih =>
      change value (h + 1)
        (addForm (h + 1) (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2))
          (entriesDecode d h es)) ρ = _
      rw [add_value, ih]
      congr 1
      change (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2)).sum
        (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) = _
      rw [Finsupp.sum_single_index]
      rw [affineValue_zero, Nat.zero_mul]

theorem literalHereditaryEvaluation : Comparators.RayCodeEvaluation.LiteralHereditaryEvaluation := by
  intro d h
  induction h with
  | zero => intro n xs; exact literalAffineEvaluation d (parseCoefficients n) xs
  | succ h ih =>
      intro n xs
      change (parseEntries n).foldr
        (fun e acc => affineEval d e.2 xs * 2 ^ evalCode d h e.1 xs + acc) 0 =
          value (h + 1) (entriesDecode d h (parseEntries n)) (fun i => xs.getD i.val 0)
      rw [entries_value]
      have haff : ∀ c xs, affineEval d c xs =
          affineValue (coeffDecode d c) (fun i => xs.getD i.val 0) := literalAffineEvaluation d
      simp only [haff, ih]

private theorem pr_pow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem pr_affineEval : Primrec (fun p : Nat × CoeffCode × List Nat => affineEval p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × CoeffCode × List Nat => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat × CoeffCode × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Nat × CoeffCode × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (p : Nat × CoeffCode × List Nat) (q : Nat × Nat) =>
      p.2.1.getD (q.1 + 1) 0 * p.2.2.getD q.1 0 + q.2) := by
    exact (Primrec.nat_add.comp (Primrec.nat_mul.comp
      ((Primrec.list_getD 0).comp (hc.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
      ((Primrec.list_getD 0).comp (hx.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.nat_add.comp ((Primrec.list_getD 0).comp hc (Primrec.const 0))
    (Primrec.list_foldr (Primrec.list_range.comp hd) (Primrec.const 0) hstep)

private def assembleRows (d : Nat) (es : MapCode) (xs rs : List Nat) : Nat :=
  (List.range es.length).foldr (fun i acc =>
    affineEval d (es.getD i (0, [])).2 xs * 2 ^ rs.getD i 0 + acc) 0

private theorem assembleRows_map (d : Nat) (es : MapCode) (xs : List Nat)
    (F : Nat × CoeffCode → Nat) :
    assembleRows d es xs (es.map F) =
      es.foldr (fun e acc => affineEval d e.2 xs * 2 ^ F e + acc) 0 := by
  have hm : (List.range es.length).map (fun i =>
      affineEval d (es.getD i (0, [])).2 xs * 2 ^ (es.map F).getD i 0) =
      es.map (fun e => affineEval d e.2 xs * 2 ^ F e) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i < es.length := by simpa using hj
      simp [hin]
  have hv := congrArg (fun ys : List Nat => ys.foldr (fun a b : Nat => a + b) 0) hm
  simpa only [List.foldr_map, assembleRows] using hv

private theorem pr_assembleRows : Primrec (fun p : Nat × MapCode × List Nat × List Nat =>
    assembleRows p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hd : Primrec (fun p : Nat × MapCode × List Nat × List Nat => p.1) := Primrec.fst
  have he : Primrec (fun p : Nat × MapCode × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Nat × MapCode × List Nat × List Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : Nat × MapCode × List Nat × List Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (p : Nat × MapCode × List Nat × List Nat) (q : Nat × Nat) =>
      affineEval p.1 (p.2.1.getD q.1 (0, [])).2 p.2.2.1 * 2 ^ p.2.2.2.getD q.1 0 + q.2) := by
    have hcoeff : Primrec (fun q : (Nat × MapCode × List Nat × List Nat) × (Nat × Nat) =>
        (q.1.2.1.getD q.2.1 (0, [])).2) := Primrec.snd.comp ((Primrec.list_getD (0, ([] : CoeffCode))).comp
      (he.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    have heval := pr_affineEval.comp ((hd.comp Primrec.fst).pair
      (hcoeff.pair (hx.comp Primrec.fst)))
    have hpow : Primrec (fun q : (Nat × MapCode × List Nat × List Nat) × (Nat × Nat) =>
        2 ^ q.1.2.2.2.getD q.2.1 0) := pr_pow.comp (Primrec.const 2)
      ((Primrec.list_getD 0).comp (hr.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    exact (Primrec.nat_add.comp (Primrec.nat_mul.comp heval hpow)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.list_range.comp (Primrec.list_length.comp he))
    (Primrec.const 0) hstep

private def evalChildren (p : Nat × Nat × Nat × List Nat) :
    List (Nat × Nat × Nat × List Nat) :=
  if p.2.1 = 0 then [] else
    (parseEntries p.2.2.1).map (fun e => (p.1, p.2.1 - 1, e.1, p.2.2.2))

private def evalAssemble (p : Nat × Nat × Nat × List Nat) (rs : List Nat) : Option Nat :=
  some (if p.2.1 = 0 then affineEval p.1 (parseCoefficients p.2.2.1) p.2.2.2
    else assembleRows p.1 (parseEntries p.2.2.1) p.2.2.2 rs)

private theorem pr_evalChildren : Primrec evalChildren := by
  have hd : Primrec (fun p : Nat × Nat × Nat × List Nat => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  apply Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) (Primrec.const [])
  apply Primrec.list_map (pr_parseEntries.comp hn)
  exact ((hd.comp Primrec.fst).pair
    ((Primrec.nat_sub.comp (hh.comp Primrec.fst) (Primrec.const 1)).pair
      ((Primrec.fst.comp Primrec.snd).pair (hx.comp Primrec.fst)))).to₂

private theorem pr_evalBase : Primrec (fun p : Nat × Nat × Nat × List Nat =>
    affineEval p.1 (parseCoefficients p.2.2.1) p.2.2.2) := by
  have hd : Primrec (fun p : Nat × Nat × Nat × List Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact pr_affineEval.comp (hd.pair ((pr_parseCoefficients.comp hn).pair hx))

private theorem pr_evalRows : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat =>
    assembleRows q.1.1 (parseEntries q.1.2.2.1) q.1.2.2.2 q.2) := by
  have hd : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have he : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat => parseEntries q.1.2.2.1) :=
    pr_parseEntries.comp hn
  have hx : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat => q.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hr : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat => q.2) := Primrec.snd
  have hargs : Primrec (fun q : (Nat × Nat × Nat × List Nat) × List Nat =>
      (q.1.1, parseEntries q.1.2.2.1, q.1.2.2.2, q.2)) := hd.pair (he.pair (hx.pair hr))
  exact (pr_assembleRows.comp hargs).of_eq (fun _ => rfl)

private theorem pr_evalAssemble : Primrec₂ evalAssemble := by
  have hh : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  exact (Primrec.option_some.comp (Primrec.ite
    ((Primrec.eq.comp hh (Primrec.const 0)).comp Primrec.fst)
    (pr_evalBase.comp Primrec.fst) pr_evalRows)).to₂

theorem pr_evalCode : Primrec (fun p : Nat × Nat × Nat × List Nat =>
    evalCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : Nat × Nat × Nat × List Nat → Nat := fun p => evalCode p.1 p.2.1 p.2.2.1 p.2.2.2
  have hh : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  apply Primrec.nat_omega_rec' f hh pr_evalChildren pr_evalAssemble
  · intro p q hq
    by_cases h0 : p.2.1 = 0
    · simp [evalChildren, h0] at hq
    · have hmap : q ∈ (parseEntries p.2.2.1).map
          (fun e => (p.1, p.2.1 - 1, e.1, p.2.2.2)) := by
        simpa only [evalChildren, if_neg h0] using hq
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmap
      dsimp
      omega
  · rintro ⟨d, h, n, xs⟩
    cases h with
    | zero => rfl
    | succ h => simp [evalChildren, evalAssemble, f, evalCode, List.map_map, assembleRows_map]

theorem actualUniformPrograms : Comparators.RayCodeEvaluation.ActualUniformPrograms :=
  ⟨pr_affineEval, pr_evalCode⟩

theorem rayCodeEvaluation : Comparators.RayCodeEvaluation.Target :=
  ⟨literalAffineEvaluation, literalHereditaryEvaluation, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.RayCodeEvaluationProof
