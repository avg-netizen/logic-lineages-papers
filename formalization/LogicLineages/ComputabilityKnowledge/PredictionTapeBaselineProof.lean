module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineProof
open PredictionTapeObservation PredictionTapeBaseline PredictionTapeBaselineTargets
open PredictionRobust (historyPrefix budgetPrefix)

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
      (∀ r, r < xs.length → historicalTest i budgets xs ys r = true) ∧
        (boundedMove i (budgets.getD xs.length 0) ys).isSome = true := by
  simp only [eligible, Bool.and_eq_true, List.all_eq_true, List.mem_range]

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
    ∃ v, observe (selectedIndex budgets xs ys) (budgets.getD xs.length 0) ys = some v ∧
      PredictionUniformBinaryCompiler.readBit v = some (baseline budgets xs ys) := by
  obtain ⟨_, hm⟩ := (eligibility _ _ _ _).mp he
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hz
  have hb : baseline budgets xs ys = z := by
    simp only [baseline, if_pos hi, indexedMove, hz, Option.getD_some]
  exact ⟨v, hv, by simpa [hb] using hd⟩

theorem wrongSelectionExcluded : WrongSelectionExcluded := by
  intro b x y n m hnm i hi he hw
  obtain ⟨v, hv, hd⟩ := selected_output _ _ _ (by simpa [prefix_length] using hi) he
  have hv' : observe i (b n) (historyPrefix y n) = some v := by
    rw [prefix_length] at hv
    change observe i ((historyPrefix b (n + 1)).getD n 0) (historyPrefix y n) = some v at hv
    rw [prefix_getD b (n + 1) n 0 (Nat.lt_succ_self n)] at hv
    exact hv
  have hvne : v ≠ PredictionFiniteAlphabet.inputSymbol (x n) := by
    intro h
    have heq := (PredictionUniformBinaryCompilerProof.physicalBinaryReadout v (x n)).2 h
    exact hw (Option.some.inj (hd.symm.trans heq))
  apply Bool.eq_false_iff.mpr
  intro hm
  obtain ⟨hh, _⟩ := (eligibility _ _ _ _).mp hm
  have hh := hh n (by simpa [prefix_length] using hnm)
  rw [historicalTest, prefix_take y m n (Nat.le_of_lt hnm)] at hh
  rw [show (budgetPrefix b m).getD n 0 = b n by exact prefix_getD b (m + 1) n 0 (by omega),
    prefix_getD x m n false hnm, hv'] at hh
  simpa [hvne] using hh

theorem trueProgramEventuallyEligible : TrueProgramEventuallyEligible := by
  intro e hp b y ha x
  obtain ⟨N, hN⟩ := ha
  refine ⟨max N e, fun n hn => ⟨by omega, ?_⟩⟩
  apply (eligibility _ _ _ _).mpr
  constructor
  · intro r hr
    have hrn : r < n := by simpa [prefix_length] using hr
    simp only [historicalTest]
    rw [prefix_take y n r (Nat.le_of_lt hrn)]
    cases hv : observe e ((budgetPrefix b n).getD r 0) (historyPrefix y r) with
    | none => rfl
    | some v =>
      have hvv : v = PredictionFiniteAlphabet.inputSymbol (policy e hp (historyPrefix y r)) :=
        PredictionTapeObservationProof.observationUniqueOnTotal e hp _ _ v hv
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
  have hs : ∀ n, N ≤ n → sel n ≤ e ∧
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
  let bound := (Finset.range (e + 1)).sup C
  refine ⟨max N bound, fun n hn => ?_⟩
  have hNn : N ≤ n := by omega
  have hle := (hs n hNn).1
  have hbound : C (sel n) ≤ bound := Finset.le_sup (by simp; omega)
  exact not_not.mp (hC (sel n) n (by omega) hNn rfl)

/-! Uniform primitive recursiveness of the actual finite-input operation.
No time bound or computable totality test is inferred. -/
private abbrev Data := List Nat × List Bool × List Bool
private abbrev HistData := Nat × Data

private theorem pr_observe : Primrec (fun z : Nat × Nat × List Bool => observe z.1 z.2.1 z.2.2) :=
  PredictionTapeObservationProof.effectiveObservation.1

private theorem pr_move : Primrec (fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2) :=
  PredictionTapeObservationProof.effectiveObservation.2

private theorem pr_inputSymbol : Primrec PredictionFiniteAlphabet.inputSymbol := Primrec.dom_finite _

private theorem pr_history : Primrec (fun z : HistData × Nat =>
    historicalTest z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hc : Primrec (fun z : HistData × Nat => z.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun z : HistData × Nat => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun z : HistData × Nat => z.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hy : Primrec (fun z : HistData × Nat => z.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hv : Primrec (fun z : HistData × Nat => observe z.1.1
      (z.1.2.1.getD z.2 0) (z.1.2.2.2.take z.2)) :=
    Primrec.comp (f := fun z : Nat × Nat × List Bool => observe z.1 z.2.1 z.2.2)
      (g := fun z : HistData × Nat => (z.1.1, z.1.2.1.getD z.2 0, z.1.2.2.2.take z.2))
      pr_observe (hc.pair (((Primrec.list_getD 0).comp hb Primrec.snd).pair
        (Primrec.list_take.comp Primrec.snd hy)))
  have hbit : Primrec (fun z : HistData × Nat => PredictionFiniteAlphabet.inputSymbol (z.1.2.2.1.getD z.2 false)) :=
    pr_inputSymbol.comp ((Primrec.list_getD false).comp hx Primrec.snd)
  apply (Primrec.option_casesOn hv (Primrec.const true)
    ((Primrec.eq.comp Primrec.snd (hbit.comp Primrec.fst)).decide).to₂).of_eq
  intro z
  unfold historicalTest
  cases observe z.1.1 (z.1.2.1.getD z.2 0) (z.1.2.2.2.take z.2) <;> rfl

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
  Primrec.comp (f := fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2)
    (g := fun z : HistData => (z.1, z.2.1.getD z.2.2.1.length 0, z.2.2.2)) pr_move
    (Primrec.fst.pair (((Primrec.list_getD 0).comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem pr_eligible : Primrec (fun z : Data × Nat =>
    eligible z.1.1 z.1.2.1 z.1.2.2 z.2) :=
  (Primrec.and.comp (pr_allHistory.comp (Primrec.snd.pair Primrec.fst))
    (Primrec.option_isSome.comp (pr_current.comp (Primrec.snd.pair Primrec.fst)))).of_eq (fun _ => rfl)

private theorem pr_selected : Primrec (fun z : Data => selectedIndex z.1 z.2.1 z.2.2) :=
  Primrec.list_findIdx
    (Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))) pr_eligible.to₂

private theorem pr_indexed : Primrec (fun z : Data × Nat => indexedMove z.1.1 z.1.2.1 z.1.2.2 z.2) :=
  (pr_current.comp (Primrec.snd.pair Primrec.fst)).of_eq (fun _ => rfl)

theorem primitiveRecursiveBaseline : PrimitiveRecursiveBaseline := by
  have hcond : PrimrecPred (fun z : Data => selectedIndex z.1 z.2.1 z.2.2 ≤ z.2.1.length) :=
    Primrec.nat_le.comp pr_selected (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
  exact Primrec.ite hcond
    (Primrec.option_getD.comp (pr_indexed.comp (Primrec.id.pair pr_selected)) (Primrec.const false))
    (Primrec.const false) |>.of_eq (fun _ => rfl)

end LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineProof
