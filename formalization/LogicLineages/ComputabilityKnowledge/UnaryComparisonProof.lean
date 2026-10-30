module

public import LogicLineages.ComputabilityKnowledge.Comparators.UnaryComparison
public import LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! External full unary comparison proof after target freeze. The finite
scan is over 1..T, including the first stable point; its least-failure law is
proved, and the unary ray is proved to be exactly the original input n. -/
namespace LogicLineages.ComputabilityKnowledge.UnaryComparisonProof

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open CircuitReduction FiniteComparisonEnumeration RayFamilyClosure
open UnaryComparison

theorem unaryRayIdentity : Comparators.UnaryComparison.UnaryRayIdentity := by
  have hw : ∀ roots : List HeightCode, RaySeparation.weights 1 roots = [1] := by
    intro roots
    simp [RaySeparation.weights, RayCoefficientCollection.sharedWeights, AffineRayCalibration.weights]
  refine ⟨hw, ?_⟩
  intro roots p t
  constructor
  · unfold RaySeparation.originalValue
    rw [hw]
    congr 1
    funext i
    have hi : i.val = 0 := by omega
    simp [hi]
  · rw [RayCodeEvaluationProof.literalHereditaryEvaluation]
    congr 1
    funext i
    have hi : i.val = 0 := by omega
    simp [hi]

private theorem scan_none (weak : Bool) (pq : HeightCode × HeightCode) (xs : List Nat) :
    xs.foldr (fun i acc => if holdsAt weak pq (i + 1) then acc else some (i + 1)) none = none ↔
      ∀ i ∈ xs, holdsAt weak pq (i + 1) = true := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      cases h : holdsAt weak pq (i + 1) <;> simp [h, ih]

private theorem scan_find (weak : Bool) (pq : HeightCode × HeightCode) (xs : List Nat) :
    xs.foldr (fun i acc => if holdsAt weak pq (i + 1) then acc else some (i + 1)) none =
      (xs.map (fun i => i + 1)).find? (fun n => !(holdsAt weak pq n)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : holdsAt weak pq (i + 1) <;> simp [h, ih]

private theorem firstFailure_find (weak : Bool) (pq : HeightCode × HeightCode) (T : Nat) :
    firstFailure weak pq T =
      (List.ofFn (fun i : Fin T => i.val + 1)).find? (fun n => !(holdsAt weak pq n)) := by
  rw [firstFailure, scan_find]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem exactFiniteScan : Comparators.UnaryComparison.ExactFiniteScan := by
  intro weak pq T
  constructor
  · rw [firstFailure, scan_none]
    constructor
    · intro h n hn hT
      have hi : n - 1 ∈ List.range T := List.mem_range.mpr (by omega)
      have hh := h (n - 1) hi
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hh
    · intro h i hi
      exact h (i + 1) (by omega) (by have := List.mem_range.mp hi; omega)
  · intro n
    rw [firstFailure_find, List.find?_ofFn_eq_some]
    constructor
    · rintro ⟨hbad, i, hin, hprev⟩
      have hn : 0 < n := by omega
      have hnT : n ≤ T := by have := i.isLt; omega
      refine ⟨hn, hnT, by simpa using hbad, ?_⟩
      intro m hm hmn
      let j : Fin T := ⟨m - 1, by omega⟩
      have hji : j < i := by change m - 1 < i.val; omega
      have hj := hprev j hji
      have hjn : j.val + 1 = m := by dsimp [j]; omega
      rw [hjn] at hj
      simpa using hj
    · rintro ⟨hn, hnT, hbad, hprev⟩
      let i : Fin T := ⟨n - 1, by omega⟩
      refine ⟨by simpa using hbad, i, by dsimp [i]; omega, ?_⟩
      intro j hji
      have hj := hprev (j.val + 1) (by omega) (by change j.val < i.val at hji; dsimp [i] at hji; omega)
      simp [hj]

theorem provedEventualComparison : Comparators.UnaryComparison.ProvedEventualComparison := by
  intro weak pq hsource
  let roots := [pq.1, pq.2]
  have hp := (RayFamilyClosureProof.originalMembersAndZero 1 roots).1 pq.1 (by simp [roots])
  have hq := (RayFamilyClosureProof.originalMembersAndZero 1 roots).1 pq.2 (by simp [roots])
  have ht : 0 < boundCode pq := (RaySeparationProof.positiveEffectiveRay 1 roots).2.1
  refine ⟨ht, ?_⟩
  intro n hn
  have h := (RaySeparationProof.computedEventualSigns).2 1 roots hsource pq.1 hp pq.2 hq n hn
  have hT := (RaySeparationProof.computedEventualSigns).2 1 roots hsource pq.1 hp pq.2 hq (boundCode pq) le_rfl
  have hlt := h.2.1.symm.trans hT.2.1
  have hrev := h.2.2.symm.trans hT.2.2
  have eval_eq (p : HeightCode) (t : Nat) : RayCodeEvaluation.evalCode 1 p.1 p.2 [t] =
      RaySeparation.originalValue 1 roots p t :=
    (unaryRayIdentity.2 roots p t).2.trans (unaryRayIdentity.2 roots p t).1.symm
  cases weak with
  | false =>
      simp only [holdsAt, Bool.false_eq_true, ↓reduceIte, eval_eq]
      exact decide_eq_decide.mpr hlt
  | true =>
      have hle := not_congr hrev
      simp only [not_lt] at hle
      simp only [holdsAt, ↓reduceIte, eval_eq]
      exact decide_eq_decide.mpr hle

theorem exactRawDomain : Comparators.UnaryComparison.ExactRawDomain := by
  intro weak a b
  have h := (ExponentialIdentityProof.exactRawDomain 1 a b).1
  simpa only [ExponentialIdentity.decisionCode, resultCode, decisionCode, Option.isSome_map] using And.intro h h

private theorem source_data (weak : Bool) (a b : Expr (Fin 1)) :
    ∃ pq : HeightCode × HeightCode,
      ExponentialIdentity.normalInputs 1 (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) = some pq ∧
      SourceFamily 1 [pq.1, pq.2] ∧
      ∀ n : PosNat, holdsAt weak pq n = true ↔ Holds weak a b n := by
  obtain ⟨j, hj, hcj, hwj, hvj⟩ := ExponentialNormalizerProgramSemantics.fullEffectiveNormalization 1 a
  obtain ⟨k, hk, hck, hwk, hvk⟩ := ExponentialNormalizerProgramSemantics.fullEffectiveNormalization 1 b
  let p : HeightCode := (a.depth, j)
  let q : HeightCode := (b.depth, k)
  refine ⟨(p, q), ?_, ?_, ?_⟩
  · simp [ExponentialIdentity.normalInputs, hj, hk, p, q]
  · intro r hr
    simp at hr
    rcases hr with rfl | rfl
    · exact ⟨hcj, hwj⟩
    · exact ⟨hck, hwk⟩
  · intro n
    have hp : RayCodeEvaluation.evalCode 1 p.1 p.2 [(n : Nat)] = a.eval (fun _ => n) :=
      (unaryRayIdentity.2 [] p n).2.trans (hvj (fun _ => n))
    have hq : RayCodeEvaluation.evalCode 1 q.1 q.2 [(n : Nat)] = b.eval (fun _ => n) :=
      (unaryRayIdentity.2 [] q n).2.trans (hvk (fun _ => n))
    cases weak <;> simp [holdsAt, Holds, hp, hq]

theorem sourceResult : Comparators.UnaryComparison.SourceResult := by
  intro weak a b
  obtain ⟨pq, hin, hsource, hsem⟩ := source_data weak a b
  have hb := provedEventualComparison weak pq hsource
  have hs := exactFiniteScan weak pq (boundCode pq)
  have hres : resultCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some (firstFailure weak pq (boundCode pq)) := by simp [resultCode, hin]
  rw [hres]
  constructor
  · simp only [Option.some.injEq]
    rw [hs.1]
    constructor
    · intro h n
      apply (hsem n).mp
      by_cases hn : (n : Nat) ≤ boundCode pq
      · exact h n n.property hn
      · rw [hb.2 n (by omega)]
        exact h _ hb.1 le_rfl
    · intro h n hn hnT
      exact (hsem ⟨n, hn⟩).mpr (h ⟨n, hn⟩)
  · intro n
    simp only [Option.some.injEq]
    rw [hs.2 n]
    constructor
    · rintro ⟨hn, hnT, hbad, hprev⟩
      refine ⟨hn, ?_, ?_⟩
      · intro h
        have ht := (hsem ⟨n, hn⟩).mpr h
        simp [hbad] at ht
      · intro m hmn
        exact (hsem m).mp (hprev m m.property hmn)
    · rintro ⟨hn, hbad, hprev⟩
      have hf : holdsAt weak pq n = false := by
        cases hval : holdsAt weak pq n with
        | false => rfl
        | true => exact False.elim (hbad ((hsem ⟨n, hn⟩).mp hval))
      have hnT : n ≤ boundCode pq := by
        by_contra hh
        have hsmall := (hsem ⟨boundCode pq, hb.1⟩).mpr (hprev ⟨boundCode pq, hb.1⟩ (by change boundCode pq < n; omega))
        have hstable := hb.2 n (by omega)
        simp [hf, hsmall] at hstable
      exact ⟨hn, hnT, hf, fun m hm hmn => (hsem ⟨m, hm⟩).mpr (hprev ⟨m, hm⟩ hmn)⟩

theorem sourceDecision : Comparators.UnaryComparison.SourceDecision := by
  intro weak a b
  obtain ⟨pq, hin, hsource, hsem⟩ := source_data weak a b
  have hs := (sourceResult weak a b).1
  have hres : resultCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some (firstFailure weak pq (boundCode pq)) := by simp [resultCode, hin]
  cases hf : firstFailure weak pq (boundCode pq) with
  | none =>
      have hu : ∀ n, Holds weak a b n := hs.mp (by simpa [hf] using hres)
      simp [decisionCode, hres, hf, hu]
  | some n =>
      have hu : ¬∀ n, Holds weak a b n := by
        intro h
        have hh := hs.mpr h
        rw [hres, hf] at hh
        simp at hh
      simp only [decisionCode, hres, hf, Option.map_some]
      constructor
      · constructor
        · intro h; simp at h
        · intro h; exact False.elim (hu h)
      · exact ⟨fun _ => hu, fun _ => rfl⟩

theorem pr_boundCode : Primrec boundCode := by
  have hr : Primrec (fun pq : HeightCode × HeightCode => [pq.1, pq.2]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact (RaySeparationProof.pr_threshold.comp ((Primrec.const 1).pair hr)).of_eq (fun _ => rfl)

private theorem pr_unaryEval : Primrec (fun p : HeightCode × Nat =>
    RayCodeEvaluation.evalCode 1 p.1.1 p.1.2 [p.2]) := by
  have hh : Primrec (fun p : HeightCode × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : HeightCode × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun p : HeightCode × Nat => [p.2]) := Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  have hargs : Primrec (fun p : HeightCode × Nat => (1, p.1.1, p.1.2, [p.2])) :=
    (Primrec.const 1).pair (hh.pair (hn.pair hx))
  exact (RayCodeEvaluationProof.pr_evalCode.comp hargs).of_eq (fun _ => rfl)

theorem pr_holdsAt : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => holdsAt p.1 p.2.1 p.2.2) := by
  have hw : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => p.1) := Primrec.fst
  have hp : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hq : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha := pr_unaryEval.comp (hp.pair hn)
  have hb := pr_unaryEval.comp (hq.pair hn)
  exact Primrec.ite (Primrec.eq.comp hw (Primrec.const true))
    (Primrec.nat_le.comp ha hb).decide (Primrec.nat_lt.comp ha hb).decide

theorem pr_firstFailure : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat =>
    firstFailure p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (p : Bool × (HeightCode × HeightCode) × Nat) (q : Nat × Option Nat) =>
      if holdsAt p.1 p.2.1 (q.1 + 1) then q.2 else some (q.1 + 1)) := by
    have hn : Primrec (fun q : (Bool × (HeightCode × HeightCode) × Nat) × (Nat × Option Nat) => q.2.1 + 1) :=
      Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
    have ha : Primrec (fun q : (Bool × (HeightCode × HeightCode) × Nat) × (Nat × Option Nat) =>
        holdsAt q.1.1 q.1.2.1 (q.2.1 + 1)) :=
      pr_holdsAt.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair hn))
    exact (Primrec.ite (Primrec.eq.comp ha (Primrec.const true))
      (Primrec.snd.comp Primrec.snd) (Primrec.option_some.comp hn)).to₂
  exact Primrec.list_foldr (Primrec.list_range.comp ht) (Primrec.const none) hstep

theorem pr_resultCode : Primrec (fun p : Bool × List Nat × List Nat => resultCode p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : Bool × List Nat × List Nat => ExponentialIdentity.normalInputs 1 p.2.1 p.2.2) :=
    ExponentialIdentityProof.pr_normalInputs.comp ((Primrec.const 1).pair Primrec.snd)
  have hstep : Primrec₂ (fun (p : Bool × List Nat × List Nat) (pq : HeightCode × HeightCode) =>
      firstFailure p.1 pq (boundCode pq)) := by
    have hargs : Primrec (fun q : (Bool × List Nat × List Nat) × (HeightCode × HeightCode) =>
        (q.1.1, q.2, boundCode q.2)) :=
      (Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair (pr_boundCode.comp Primrec.snd))
    exact ((pr_firstFailure.comp hargs).of_eq (fun _ => rfl)).to₂
  exact Primrec.option_map hp hstep

private theorem pr_isNone : Primrec (Option.isNone : Option Nat → Bool) :=
  ((Primrec.eq.comp Primrec.option_isSome (Primrec.const false)).decide).of_eq (by intro o; cases o <;> rfl)

theorem pr_decisionCode : Primrec (fun p : Bool × List Nat × List Nat => decisionCode p.1 p.2.1 p.2.2) :=
  Primrec.option_map pr_resultCode (pr_isNone.comp Primrec.snd).to₂

theorem actualUniformPrograms : Comparators.UnaryComparison.ActualUniformPrograms :=
  ⟨pr_boundCode, pr_holdsAt, pr_firstFailure, pr_resultCode, pr_decisionCode⟩

theorem unaryComparison : Comparators.UnaryComparison.Target :=
  ⟨unaryRayIdentity, exactFiniteScan, provedEventualComparison, exactRawDomain,
    sourceResult, sourceDecision, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.UnaryComparisonProof
