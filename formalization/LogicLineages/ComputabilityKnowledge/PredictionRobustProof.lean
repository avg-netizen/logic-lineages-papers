module

public import LogicLineages.ComputabilityKnowledge.PredictionRobustTargets
public import LogicLineages.ComputabilityKnowledge.PredictionLearningProof
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRobustProof
open PredictionLearning PredictionRobust PredictionRobustTargets

private theorem prefix_length {α : Type} (s : Nat → α) (n : Nat) :
    (historyPrefix s n).length = n := by simp [historyPrefix]

private theorem prefix_getD {α : Type} (s : Nat → α) (n r : Nat) (d : α) (h : r < n) :
    (historyPrefix s n).getD r d = s r := by simp [historyPrefix, h]

private theorem prefix_take {α : Type} (s : Nat → α) (n r : Nat) (h : r ≤ n) :
    (historyPrefix s n).take r = historyPrefix s r := by
  apply List.ext_getElem
  · simp [historyPrefix, Nat.min_eq_left h]
  · intro i hi hj
    simp [historyPrefix]

private theorem eligibility (budgets : List Nat) (xs ys : List Bool) (i : Nat) :
    eligible budgets xs ys i = true ↔
      ∃ c, Encodable.decode (α := Code) i = some c ∧
        (∀ r, r < xs.length → historicalTest c budgets xs ys r = true) ∧
        (boundedMove c (budgets.getD xs.length 0) ys).isSome = true := by
  cases h : Encodable.decode (α := Code) i <;> simp only [eligible, h, Option.some.injEq, reduceCtorEq, Bool.and_eq_true, List.all_eq_true, List.mem_range, false_and, exists_false, Bool.false_eq_true]
  constructor
  · intro hh; exact ⟨_, rfl, hh⟩
  · rintro ⟨c, rfl, hh⟩; exact hh

theorem leastEligibleSelection : LeastEligibleSelection := by
  intro budgets xs ys k hk he
  let p := eligible budgets xs ys
  have hlt : (List.range (xs.length + 1)).findIdx p < xs.length + 1 := by
    simpa using List.findIdx_lt_length_of_exists
      (xs := List.range (xs.length + 1)) ⟨k, by simp; omega, he⟩
  have hsel : p ((List.range (xs.length + 1)).findIdx p) = true := by
    have ht := List.findIdx_getElem (xs := List.range (xs.length + 1))
      (p := p) (w := by simpa using hlt)
    have hv : (List.range (xs.length + 1))[(List.range (xs.length + 1)).findIdx p]'(by simpa using hlt) =
        (List.range (xs.length + 1)).findIdx p := List.getElem_range _
    exact (congrArg p hv).symm.trans ht
  have hle : (List.range (xs.length + 1)).findIdx p ≤ k := by
    by_contra hn
    have hfalse := List.not_of_lt_findIdx (xs := List.range (xs.length + 1))
      (p := p) (by omega : k < (List.range (xs.length + 1)).findIdx p)
    have : p k = false := by simpa using hfalse
    simp [p, he] at this
  exact ⟨hle, hsel⟩

private theorem selected_output (budgets : List Nat) (xs ys : List Bool)
    (hi : selectedIndex budgets xs ys ≤ xs.length)
    (he : eligible budgets xs ys (selectedIndex budgets xs ys) = true) :
    ∃ c v, Encodable.decode (α := Code) (selectedIndex budgets xs ys) = some c ∧
      Nat.Partrec.Code.evaln (budgets.getD xs.length 0) c (Encodable.encode ys) = some v ∧
      decodeBit v = some (baseline budgets xs ys) := by
  obtain ⟨c, hc, _, hm⟩ := (eligibility _ _ _ _).mp he
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨v, hv, hd⟩ := (PredictionLearningProof.bind_some_iff _ _ _).mp hz
  have hb : baseline budgets xs ys = z := by
    simp only [baseline, if_pos hi, indexedMove, hc, Option.bind_some, hz, Option.getD_some]
  exact ⟨c, v, hc, hv, by simpa [hb] using hd⟩

private theorem bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitValue]

theorem wrongSelectionExcluded : WrongSelectionExcluded := by
  intro b x y n m hnm i hi he hw
  obtain ⟨c, v, hc, hv, hd⟩ := selected_output _ _ _ (by simpa [prefix_length] using hi) he
  have hv' : Nat.Partrec.Code.evaln (b n) c (Encodable.encode (historyPrefix y n)) = some v := by
    rw [prefix_length] at hv
    change Nat.Partrec.Code.evaln ((historyPrefix b (n + 1)).getD n 0) c
      (Encodable.encode (historyPrefix y n)) = some v at hv
    rw [prefix_getD b (n + 1) n 0 (Nat.lt_succ_self n)] at hv
    exact hv
  have hvne : v ≠ bitValue (x n) := by
    intro h
    rw [h, PredictionLearningProof.decode_bitValue] at hd
    exact hw (Option.some.inj hd).symm
  apply Bool.eq_false_iff.mpr
  intro hm
  obtain ⟨c', hc', hh, _⟩ := (eligibility _ _ _ _).mp hm
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  have hh := hh n (by simpa [prefix_length] using hnm)
  rw [historicalTest, prefix_take y m n (Nat.le_of_lt hnm)] at hh
  rw [show (budgetPrefix b m).getD n 0 = b n by exact prefix_getD b (m + 1) n 0 (by omega),
    prefix_getD x m n false hnm, hv'] at hh
  simpa [hvne] using hh

theorem trueProgramEventuallyEligible : TrueProgramEventuallyEligible := by
  intro e hp b y ha x
  obtain ⟨N, hN⟩ := ha
  refine ⟨max N (Encodable.encode e), fun n hn => ⟨by omega, ?_⟩⟩
  apply (eligibility _ _ _ _).mpr
  refine ⟨e, Encodable.encodek e, ?_, ?_⟩
  · intro r hr
    have hrn : r < n := by simpa [prefix_length] using hr
    simp only [historicalTest]
    rw [prefix_take y n r (Nat.le_of_lt hrn)]
    cases hv : Nat.Partrec.Code.evaln ((budgetPrefix b n).getD r 0) e
        (Encodable.encode (historyPrefix y r)) with
    | none => rfl
    | some v =>
      have hvv : v = bitValue (policy e hp (historyPrefix y r)) :=
        Part.mem_unique (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv))
          (Classical.choose_spec (hp (historyPrefix y r)))
      rw [prefix_getD x n r false hrn]
      simp [hvv, x]
  · rw [prefix_length]
    change (boundedMove e ((historyPrefix b (n + 1)).getD n 0) (historyPrefix y n)).isSome = true
    rw [prefix_getD b (n + 1) n 0 (Nat.lt_succ_self n)]
    exact congrArg Option.isSome (hN n (by omega))

theorem robustBoundedObservations : RobustBoundedObservations := by
  classical
  intro e hp b y ha x
  obtain ⟨N, hN⟩ := trueProgramEventuallyEligible e hp b y ha
  let sel := fun n => selectedIndex (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n)
  let wrong := fun n => baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) ≠ x n
  have hs : ∀ n, N ≤ n → sel n ≤ Encodable.encode e ∧
      eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) (sel n) = true := by
    intro n hn
    obtain ⟨hk, he⟩ := hN n hn
    exact leastEligibleSelection _ _ _ _ (by simpa [prefix_length] using hk) he
  have hexc : ∀ i, ∃ C, ∀ n, C ≤ n → N ≤ n → sel n = i → ¬ wrong n := by
    intro i
    by_cases h : ∃ r, N ≤ r ∧ sel r = i ∧ wrong r
    · obtain ⟨r, hr, hri, hrw⟩ := h
      refine ⟨r + 1, fun n hn hNn hni hnw => ?_⟩
      have hrsel := hs r hr
      have hno := wrongSelectionExcluded b x y r n (by omega)
        (by have := (hN r hr).1; exact le_trans hrsel.1 this) hrsel.2 hrw
      have hnsel := (hs n hNn).2
      change eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) (sel r) = false at hno
      rw [show sel r = sel n from hri.trans hni.symm] at hno
      simp [hno] at hnsel
    · exact ⟨0, fun n _ hn hni hnw => h ⟨n, hn, hni, hnw⟩⟩
  choose C hC using hexc
  let bound := (Finset.range (Encodable.encode e + 1)).sup C
  refine ⟨max N bound, fun n hn => ?_⟩
  have hNn : N ≤ n := by omega
  have hle := (hs n hNn).1
  have hbound : C (sel n) ≤ bound := Finset.le_sup (by simp; omega)
  exact not_not.mp (hC (sel n) n (by omega) hNn rfl)

/-! Uniform primitive recursiveness of the actual finite-input operation.
No time bound or computable totality test is inferred. -/
private abbrev Data := List Nat × List Bool × List Bool
private abbrev HistData := Code × Data

private theorem pr_bitValue : Primrec bitValue := by
  exact (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq (fun b => by cases b <;> rfl)

private theorem pr_history : Primrec (fun z : HistData × Nat =>
    historicalTest z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hc : Primrec (fun z : HistData × Nat => z.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun z : HistData × Nat => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun z : HistData × Nat => z.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hy : Primrec (fun z : HistData × Nat => z.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hv : Primrec (fun z : HistData × Nat => Nat.Partrec.Code.evaln
      (z.1.2.1.getD z.2 0) z.1.1 (Encodable.encode (z.1.2.2.2.take z.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.list_getD 0).comp hb Primrec.snd).pair hc |>.pair
        (Primrec.encode.comp (Primrec.list_take.comp Primrec.snd hy)))
  have hbit : Primrec (fun z : HistData × Nat => bitValue (z.1.2.2.1.getD z.2 false)) :=
    pr_bitValue.comp ((Primrec.list_getD false).comp hx Primrec.snd)
  apply (Primrec.option_casesOn hv (Primrec.const true)
    ((Primrec.eq.comp Primrec.snd (hbit.comp Primrec.fst)).decide).to₂).of_eq
  intro z
  unfold historicalTest
  cases Nat.Partrec.Code.evaln (z.1.2.1.getD z.2 0) z.1.1 (Encodable.encode (z.1.2.2.2.take z.2)) <;> rfl

private theorem pr_allHistory : Primrec (fun z : HistData =>
    (List.range z.2.2.1.length).all (historicalTest z.1 z.2.1 z.2.2.1 z.2.2.2)) := by
  have hl : Primrec (fun z : HistData => List.range z.2.2.1.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hf := Primrec.list_foldr hl (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (pr_history.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)))
  apply hf.of_eq
  intro z
  induction List.range z.2.2.1.length with
  | nil => rfl
  | cons a l ih => simp [List.all_cons, ih]

private theorem pr_current : Primrec (fun z : HistData =>
    boundedMove z.1 (z.2.1.getD z.2.2.1.length 0) z.2.2.2) :=
  PredictionLearningProof.pr_move.comp
    (Primrec.fst.pair (((Primrec.list_getD 0).comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem pr_eligible : Primrec (fun z : Data × Nat =>
    eligible z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hbody : Primrec (fun z : (Data × Nat) × Code =>
      (List.range z.1.1.2.1.length).all (historicalTest z.2 z.1.1.1 z.1.1.2.1 z.1.1.2.2) &&
      (boundedMove z.2 (z.1.1.1.getD z.1.1.2.1.length 0) z.1.1.2.2).isSome) :=
    Primrec.and.comp (pr_allHistory.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst)))
      (Primrec.option_isSome.comp (pr_current.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst))))
  exact Primrec.option_casesOn (Primrec.decode.comp Primrec.snd) (Primrec.const false) hbody.to₂

private theorem pr_selected : Primrec (fun z : Data => selectedIndex z.1 z.2.1 z.2.2) :=
  Primrec.list_findIdx
    (Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))) pr_eligible.to₂

private theorem pr_indexed : Primrec (fun z : Data × Nat => indexedMove z.1.1 z.1.2.1 z.1.2.2 z.2) :=
  Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (pr_current.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst))).to₂

theorem primitiveRecursiveBaseline : PrimitiveRecursiveBaseline := by
  have hcond : PrimrecPred (fun z : Data => selectedIndex z.1 z.2.1 z.2.2 ≤ z.2.1.length) :=
    Primrec.nat_le.comp pr_selected (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
  exact Primrec.ite hcond
    (Primrec.option_getD.comp (pr_indexed.comp (Primrec.id.pair pr_selected)) (Primrec.const false))
    (Primrec.const false)

end LogicLineages.ComputabilityKnowledge.PredictionRobustProof
