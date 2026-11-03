module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsMaskProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsLabelsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
open CommonHeadLargeGuards (Formula conjunction disjunction)
open CommonHeadLargeGuards.Proof (conjunction_eval disjunction_eval)

/-- Literal coefficients retain both sides and every original occurrence. -/
private theorem source_coefficients_row {k : Nat} (E F : BalancedSyntax.Upper k) :
    sourceCoefficients E F = (BalancedSyntax.comparisonRow E F).atoms.map Prod.fst := by
  simp only [sourceCoefficients, signedAtoms, BalancedSyntax.comparisonRow,
    List.map_append, List.map_map, Function.comp_def]

private theorem source_length {k : Nat} (E F : BalancedSyntax.Upper k) :
    (sourceCoefficients E F).length = (BalancedSyntax.comparisonRow E F).atoms.length := by
  rw [source_coefficients_row, List.length_map]

private theorem source_head {k : Nat} (E F : BalancedSyntax.Upper k) (i : Nat)
    (hi : i < (BalancedSyntax.comparisonRow E F).atoms.length) :
    sourceHeads E F i = ((BalancedSyntax.comparisonRow E F).atoms[i]).2.head := by
  have hh : (signedAtoms E F).map (fun a => a.2.head) =
      (BalancedSyntax.comparisonRow E F).atoms.map (fun a => a.2.head) := by
    simp only [signedAtoms, BalancedSyntax.comparisonRow, List.map_append,
      List.map_map, Function.comp_def, BalancedSyntax.asAtom]
  unfold sourceHeads
  rw [hh]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-- The finite mask sum is the actual collection coefficient, not a fresh
coefficient attached to the guard's labels. -/
private theorem source_blockCoefficient (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (i : Nat)
    (hi : i < (BalancedSyntax.comparisonRow E F).atoms.length) :
    blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
      (sourceValuation k Γ C E F ν) i =
    BalancedRow.Collection.blockCoefficient (BalancedSyntax.basisValues k Γ C ν)
      (BalancedSyntax.comparisonRow E F)
      (BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν)
        ((BalancedSyntax.comparisonRow E F).atoms[i]).2) := by
  classical
  unfold blockCoefficient BalancedRow.Collection.blockCoefficient
  apply congrArg List.sum
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zipIdx, source_length]
  · intro j hj hk
    have hjr : j < (BalancedSyntax.comparisonRow E F).atoms.length := by
      simpa only [List.length_map, List.length_zipIdx, source_length] using hj
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    simp only [source_coefficients_row, List.getElem_map]
    simp only [source_head E F j hjr, source_head E F i hi,
      sourceValuation_input k Γ C E F ν j hjr,
      sourceValuation_input k Γ C E F ν i hi]
    have he :
        (((BalancedSyntax.comparisonRow E F).atoms[j]).2.head =
            ((BalancedSyntax.comparisonRow E F).atoms[i]).2.head ∧
          BalancedRow.input (BalancedSyntax.basisValues k Γ C ν)
              ((BalancedSyntax.comparisonRow E F).atoms[j]).2 =
            BalancedRow.input (BalancedSyntax.basisValues k Γ C ν)
              ((BalancedSyntax.comparisonRow E F).atoms[i]).2) ↔
        BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν)
            ((BalancedSyntax.comparisonRow E F).atoms[j]).2 =
          BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν)
            ((BalancedSyntax.comparisonRow E F).atoms[i]).2 := by
      rw [BalancedRow.Collection.Proof.actualKeyIdentity]
      unfold BalancedRow.keyEqual
      rw [head_repr_eq_iff]
    simp only [he]

/-- Each original row occurrence has its literal guard label. -/
private theorem source_occurrence (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (a : Int × BalancedRow.Atom)
    (ha : a ∈ (BalancedSyntax.comparisonRow E F).atoms) :
    ∃ i < (sourceCoefficients E F).length,
      (sourceHeads E F i).1.repr = a.2.head.1.repr ∧
      sourceValuation k Γ C E F ν i =
        BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) a.2 ∧
      blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
        (sourceValuation k Γ C E F ν) i =
      BalancedRow.Collection.blockCoefficient (BalancedSyntax.basisValues k Γ C ν)
        (BalancedSyntax.comparisonRow E F)
        (BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν) a.2) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
  refine ⟨i, by rwa [source_length], ?_⟩
  rw [source_head E F i hi, sourceValuation_input k Γ C E F ν i hi,
    source_blockCoefficient k Γ C E F ν i hi, he]
  exact ⟨rfl, rfl, rfl⟩

/-- A nonzero original-label block supplies a literal collected representative
with the same actual head and complete input. -/
private theorem source_survivor_at (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (i : Nat) (hi : i < (sourceCoefficients E F).length)
    (hn : blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
      (sourceValuation k Γ C E F ν) i ≠ 0) :
    ∃ w : Int × BalancedRow.Atom,
      w ∈ (BalancedRow.Collection.collect (BalancedSyntax.basisValues k Γ C ν)
        (BalancedSyntax.comparisonRow E F)).atoms ∧
      w.1 = blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
        (sourceValuation k Γ C E F ν) i ∧
      w.2.head.1.repr = (sourceHeads E F i).1.repr ∧
      BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) w.2 =
        sourceValuation k Γ C E F ν i := by
  have hir : i < (BalancedSyntax.comparisonRow E F).atoms.length := by
    rwa [source_length] at hi
  let a := (BalancedSyntax.comparisonRow E F).atoms[i]
  have ha : a ∈ (BalancedSyntax.comparisonRow E F).atoms := List.getElem_mem hir
  have hk : BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν) a.2 ∈
      BalancedRow.Collection.keys (BalancedSyntax.basisValues k Γ C ν)
        (BalancedSyntax.comparisonRow E F) := by
    apply List.mem_dedup.mpr
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hbridge := source_blockCoefficient k Γ C E F ν i hir
  rw [hbridge] at hn
  obtain ⟨b, hb, hba, _⟩ := BalancedRow.Collection.Proof.surviving_block_complete
    (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F)
    (BalancedRow.Collection.key (BalancedSyntax.basisValues k Γ C ν) a.2) hk hn
  have he := (BalancedRow.Collection.Proof.actualKeyIdentity
    (BalancedSyntax.basisValues k Γ C ν) b a.2).mp hba
  refine ⟨(_, b), hb, hbridge.symm, ?_, ?_⟩
  · rw [source_head E F i hir]
    exact he.1
  · rw [sourceValuation_input k Γ C E F ν i hir]
    exact he.2

private theorem canceled_eval (heads : Nat → NONote) (cs : List Int)
    (ν : Nat → Nat) :
    (canceledFormula heads cs).eval ν ↔
      ∀ i < cs.length, blockCoefficient heads cs ν i = 0 := by
  simp only [canceledFormula, conjunction_eval, List.forall_mem_map, List.mem_range,
    block_eval, Int.sign_eq_zero_iff_zero]

private theorem source_canceled_iff (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) :
    (canceledFormula (sourceHeads E F) (sourceCoefficients E F)).eval
      (sourceValuation k Γ C E F ν) ↔
    (BalancedRow.Collection.collect (BalancedSyntax.basisValues k Γ C ν)
      (BalancedSyntax.comparisonRow E F)).atoms = [] := by
  rw [canceled_eval]
  constructor
  · intro hz
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨hn, hc, q, hq⟩ := BalancedRow.Collection.Proof.collected_atom
      (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F) a ha
    obtain ⟨i, hi, _, _, hb⟩ := source_occurrence k Γ C E F ν (q, a.2) hq
    apply hn
    rw [hc, ← hb, hz i hi]
  · intro hempty i hi
    by_contra hn
    obtain ⟨w, hw, _⟩ := source_survivor_at k Γ C E F ν i hi hn
    rw [hempty] at hw
    exact List.not_mem_nil hw

private theorem maximal_eval (heads : Nat → NONote) (cs : List Int)
    (i : Nat) (ν : Nat → Nat) :
    (maximalFormula heads cs i).eval ν ↔
      ∀ j < cs.length,
        ¬actualHeadKeyLess (heads i).1.repr (ν i) (heads j).1.repr (ν j) ∨
          blockCoefficient heads cs ν j = 0 := by
  simp only [maximalFormula, conjunction_eval, List.forall_mem_map, List.mem_range,
    Formula.eval, key_less_eval, block_eval, Int.sign_eq_zero_iff_zero]

private theorem source_greatest_of_label (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (i : Nat) (hi : i < (sourceCoefficients E F).length)
    (hn : blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
      (sourceValuation k Γ C E F ν) i ≠ 0)
    (hm : (maximalFormula (sourceHeads E F) (sourceCoefficients E F) i).eval
      (sourceValuation k Γ C E F ν)) :
    ∃ w : Int × BalancedRow.Atom,
      BalancedRow.CollectedDominance.GreatestSurvivor
        (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F) w ∧
      w.1 = blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
        (sourceValuation k Γ C E F ν) i := by
  obtain ⟨w, hw, hc, hh, hv⟩ := source_survivor_at k Γ C E F ν i hi hn
  refine ⟨w, ⟨hw, ?_⟩, hc⟩
  intro b hb hless
  obtain ⟨hbn, hbc, q, hq⟩ := BalancedRow.Collection.Proof.collected_atom
    (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F) b hb
  obtain ⟨j, hj, hjh, hjv, hjc⟩ := source_occurrence k Γ C E F ν (q, b.2) hq
  rcases (maximal_eval _ _ _ _).mp hm j hj with hnot | hzero
  · apply hnot
    simpa only [BalancedRow.keyLess, hh, hv, hjh, hjv] using hless
  · apply hbn
    rw [hbc, ← hjc, hzero]

private theorem source_maximal_of_greatest (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (w : Int × BalancedRow.Atom)
    (hw : BalancedRow.CollectedDominance.GreatestSurvivor
      (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F) w)
    (i : Nat)
    (hh : (sourceHeads E F i).1.repr = w.2.head.1.repr)
    (hv : sourceValuation k Γ C E F ν i =
      BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) w.2) :
    (maximalFormula (sourceHeads E F) (sourceCoefficients E F) i).eval
      (sourceValuation k Γ C E F ν) := by
  apply (maximal_eval _ _ _ _).mpr
  intro j hj
  by_cases hless : actualHeadKeyLess (sourceHeads E F i).1.repr
      (sourceValuation k Γ C E F ν i) (sourceHeads E F j).1.repr
      (sourceValuation k Γ C E F ν j)
  · right
    by_contra hn
    obtain ⟨b, hb, _, hbh, hbv⟩ := source_survivor_at k Γ C E F ν j hj hn
    apply hw.2 b hb
    simpa only [BalancedRow.keyLess, hh, hv, hbh, hbv] using hless
  · exact Or.inl hless

/-- The final labels compare two actual natural values for every integer sign,
including desired integers outside {-1,0,1}. -/
private theorem difference_sign_eval (left right : Nat) (desired : Int)
    (ν : Nat → Nat) :
    (differenceSignFormula left right desired).eval ν ↔
      Int.sign ((ν left : Int) - (ν right : Int)) = desired := by
  by_cases hn : desired = -1
  · subst desired
    simp only [differenceSignFormula, ↓reduceIte, Formula.eval,
      Int.sign_eq_neg_one_iff_neg]
    omega
  · by_cases hz : desired = 0
    · subst desired
      simp only [differenceSignFormula, hn, ↓reduceIte, Formula.eval,
        Int.sign_eq_zero_iff_zero]
      omega
    · by_cases hp : desired = 1
      · subst desired
        simp only [differenceSignFormula, hn, hz, ↓reduceIte, Formula.eval,
          Int.sign_eq_one_iff_pos]
        omega
      · simp only [differenceSignFormula, hn, hz, hp, ↓reduceIte, Formula.eval, false_iff]
        intro h
        rcases Int.sign_trichotomy ((ν left : Int) - (ν right : Int)) with hs | hs | hs
        · exact hp (h.symm.trans hs)
        · exact hz (h.symm.trans hs)
        · exact hn (h.symm.trans hs)

private theorem sign_eval (heads : Nat → NONote) (cs : List Int)
    (desired : Int) (ν : Nat → Nat) :
    (signFormula heads cs desired).eval ν ↔
      ((canceledFormula heads cs).eval ν ∧
        Int.sign ((ν cs.length : Int) - (ν (cs.length + 1) : Int)) = desired) ∨
      (desired ≠ 0 ∧ ∃ i < cs.length,
        Int.sign (blockCoefficient heads cs ν i) = desired ∧
          (maximalFormula heads cs i).eval ν) := by
  by_cases hd : desired = 0
  · simp only [signFormula, hd, ↓reduceIte, Formula.eval, difference_sign_eval,
      ne_eq, not_true_eq_false, false_and, or_false]
  · simp [signFormula, hd, Formula.eval, difference_sign_eval,
      disjunction_eval, block_eval]

private theorem source_sign_eval (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (desired : Int) (ν : Nat → Nat)
    (hE : BalancedSyntax.genuineExpression (k :: Γ) E)
    (hF : BalancedSyntax.genuineExpression (k :: Γ) F)
    (hlarge : ∀ a ∈ (BalancedSyntax.comparisonRow E F).atoms,
      BalancedRow.threshold (BalancedSyntax.comparisonRow E F) ≤
        BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) a.2) :
    (signFormula (sourceHeads E F) (sourceCoefficients E F) desired).eval
      (sourceValuation k Γ C E F ν) ↔
    Int.sign ((BalancedSyntax.value (k :: Γ) C E ν : Int) -
      (BalancedSyntax.value (k :: Γ) C F ν : Int)) = desired := by
  have hactual := BalancedRow.CollectedDominance.Proof.actualSourceDichotomy
    k Γ C E F ν hE hF hlarge
  have hlabels := literalSourceLabels k Γ C E F ν
  rw [sign_eval]
  constructor
  · rintro (⟨hc, hs⟩ | ⟨hd, i, hi, hc, hm⟩)
    · have hempty := (source_canceled_iff k Γ C E F ν).mp hc
      have he := BalancedSyntax.Affine.Proof.actualCanceledDescent k Γ C E F ν hempty
      rw [he]
      simpa only [hlabels.2.2.1, hlabels.2.2.2.1] using hs
    · have hn : blockCoefficient (sourceHeads E F) (sourceCoefficients E F)
          (sourceValuation k Γ C E F ν) i ≠ 0 := by
        intro hz
        apply hd
        rw [← hc, hz, Int.sign_zero]
      obtain ⟨w, hw, hcoef⟩ := source_greatest_of_label k Γ C E F ν i hi hn hm
      rcases hactual with hcancel | hsurvive
      · have hmem := hw.1
        rw [hcancel.1] at hmem
        exact False.elim (List.not_mem_nil hmem)
      · exact (hsurvive.2 w hw).2.trans (by rw [hcoef]; exact hc)
  · intro hs
    rcases hactual with ⟨hempty, he⟩ | ⟨⟨w, hw⟩, hsign⟩
    · left
      refine ⟨(source_canceled_iff k Γ C E F ν).mpr hempty, ?_⟩
      rw [hlabels.2.2.1, hlabels.2.2.2.1]
      rwa [he] at hs
    · obtain ⟨hn, hc, q, hq⟩ := BalancedRow.Collection.Proof.collected_atom
        (BalancedSyntax.basisValues k Γ C ν) (BalancedSyntax.comparisonRow E F) w hw.1
      obtain ⟨i, hi, hh, hv, hb⟩ := source_occurrence k Γ C E F ν (q, w.2) hq
      have hsw := (hsign w hw).2
      have hd : desired ≠ 0 := by
        intro hz
        apply hn
        apply Int.eq_zero_of_sign_eq_zero
        exact hsw.symm.trans (hs.trans hz)
      refine Or.inr ⟨hd, i, hi, ?_, source_maximal_of_greatest k Γ C E F ν w hw i hh hv⟩
      rw [hb, ← hc]
      exact hsw.symm.trans hs

/-- The bound conjunction tests every original occurrence, before cancellation. -/
private theorem source_bounds_eval (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (L : Nat) :
    (conjunction ((List.range (sourceCoefficients E F).length).map (Formula.bound L))).eval
      (sourceValuation k Γ C E F ν) ↔
      ∀ a ∈ (BalancedSyntax.comparisonRow E F).atoms,
        L ≤ BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) a.2 := by
  simp only [conjunction_eval, List.forall_mem_map, List.mem_range, Formula.eval]
  constructor
  · intro h a ha
    obtain ⟨i, hi, _, hv, _⟩ := source_occurrence k Γ C E F ν a ha
    rw [← hv]
    exact h i hi
  · intro h i hi
    have hir : i < (BalancedSyntax.comparisonRow E F).atoms.length := by
      rwa [source_length] at hi
    rw [sourceValuation_input k Γ C E F ν i hir]
    exact h _ (List.getElem_mem hir)

/-- Exact finite semantic large guard for the original source pair. The all-
cancel branch descends to the two literal lower parts under the same certificate. -/
theorem exactActualSourceLargeFormula : Targets.ExactActualSourceLargeFormula := by
  intro k Γ C E F desired ν hE hF
  change (_ ∧ (signFormula (sourceHeads E F) (sourceCoefficients E F) desired).eval
    (sourceValuation k Γ C E F ν)) ↔ _
  rw [source_bounds_eval]
  constructor
  · rintro ⟨hlarge, hsign⟩
    exact ⟨hlarge, (source_sign_eval k Γ C E F desired ν hE hF hlarge).mp hsign⟩
  · rintro ⟨hlarge, hsign⟩
    exact ⟨hlarge, (source_sign_eval k Γ C E F desired ν hE hF hlarge).mpr hsign⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
