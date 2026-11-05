module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
open NormalForm SourceRows

theorem exactFreeLinearityTest : QuantifiedLinearTargets.ExactFreeLinearityTest := by
  intro i p
  induction p with
  | matrix p => exact LinearBlockProof.isLinear_iff_occurrences i p
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [QuantifiedLinear.freeLinear, Bool.and_eq_true, QuantifiedLinear.occurrences,
        List.mem_append]
      rw [ihp, ihq]
      constructor
      · rintro ⟨hp, hq⟩ s (hs | hs) hi
        · exact hp s hs hi
        · exact hq s hs hi
      · intro h
        exact ⟨fun s hs hi => h s (Or.inl hs) hi, fun s hs hi => h s (Or.inr hs) hi⟩
  | existsNat j p ih =>
      by_cases hij : i = j
      · subst j
        constructor
        · intro _ s hs hi
          have h := (List.mem_filter.mp hs).2
          have hn : s.name ≠ i := by simpa only [bne_iff_ne] using h
          exact False.elim (hn hi)
        · intro _
          simp [QuantifiedLinear.freeLinear]
      · simp only [QuantifiedLinear.freeLinear, if_neg hij]
        rw [ih]
        constructor
        · intro h s hs hi
          exact h s (List.mem_filter.mp hs).1 hi
        · intro h s hs hi
          apply h s
          · exact List.mem_filter.mpr ⟨hs, by simpa only [bne_iff_ne, hi] using hij⟩
          · exact hi

theorem exactOutputOccurrences : QuantifiedLinearTargets.ExactOutputOccurrences := by
  intro p s
  induction p with
  | matrix p => rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [QuantifiedLinear.eliminate, LinearBlock.occurrences, LinearRows.atoms,
        List.flatMap_append, QuantifiedLinear.occurrences, List.mem_append] using
        or_congr ihp ihq
  | existsNat i p ih =>
      change s ∈ LinearBlock.occurrences (LinearRows.eliminate i (QuantifiedLinear.eliminate p)) ↔ _
      rw [LinearBlockProof.exactOneNameOccurrences i (QuantifiedLinear.eliminate p) s, ih]
      simp only [QuantifiedLinear.occurrences, List.mem_filter, bne_iff_ne]
      tauto

theorem exactOutputLinearity : QuantifiedLinearTargets.ExactOutputLinearity := by
  intro p i
  apply Bool.eq_iff_iff.mpr
  rw [LinearBlockProof.isLinear_iff_occurrences, exactFreeLinearityTest]
  constructor
  · intro h s hs hi
    exact h s ((exactOutputOccurrences p s).mpr hs) hi
  · intro h s hs hi
    exact h s ((exactOutputOccurrences p s).mp hs) hi

theorem actualQuantifierElimination : QuantifiedLinearTargets.ActualQuantifierElimination := by
  intro p
  induction p with
  | matrix p => intro _ ν; rfl
  | negative p ih =>
      intro h ν
      exact not_congr (ih h ν)
  | conjunction p q ihp ihq =>
      intro h ν
      have hh := Bool.and_eq_true_iff.mp h
      exact and_congr (ihp hh.1 ν) (ihq hh.2 ν)
  | existsNat i p ih =>
      intro h ν
      have hh := Bool.and_eq_true_iff.mp h
      have hlinear : LinearRows.isLinear i (QuantifiedLinear.eliminate p) = true := by
        rw [exactOutputLinearity p i]
        exact hh.2
      change (LinearRows.eliminate i (QuantifiedLinear.eliminate p)).eval ν ↔
        ∃ n : Nat, p.eval (Function.update ν i n)
      rw [LinearRowsSemanticProof.actualLinearElimination i (QuantifiedLinear.eliminate p) hlinear ν]
      exact exists_congr (fun n => ih hh.1 (Function.update ν i n))

theorem exactFreeVariableSupport : QuantifiedLinearTargets.ExactFreeVariableSupport := by
  intro p v
  induction p with
  | matrix p => rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [QuantifiedLinear.eliminate, Formula.variables, QFormula.variables,
        List.mem_append] using or_congr ihp ihq
  | existsNat i p ih =>
      change v ∈ (LinearRows.eliminate i (QuantifiedLinear.eliminate p)).variables ↔ _
      rw [LinearRowsSupportProof.exactOutputSupport i (QuantifiedLinear.eliminate p) v, ih]
      simp only [QFormula.variables, List.mem_filter, bne_iff_ne]
      tauto

theorem freeLinear_bindAll (names : List Nat) (p : Formula) (i : Nat) :
    QuantifiedLinear.freeLinear i (bindAll names (.matrix p)) =
      (if i ∈ names then true else LinearRows.isLinear i p) := by
  induction names with
  | nil => simp [bindAll, QuantifiedLinear.freeLinear]
  | cons j names ih =>
      change (if i = j then true else
        QuantifiedLinear.freeLinear i (bindAll names (.matrix p))) = _
      rw [ih]
      by_cases hij : i = j <;> by_cases hin : i ∈ names <;> simp [hij, hin]

theorem admissible_bindAll (names : List Nat) (p : Formula) :
    QuantifiedLinear.admissible (bindAll names (.matrix p)) = LinearBlock.allLinear names p := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      change (QuantifiedLinear.admissible (bindAll names (.matrix p)) &&
        QuantifiedLinear.freeLinear i (bindAll names (.matrix p))) = _
      rw [ih, freeLinear_bindAll]
      change (LinearBlock.allLinear names p &&
        (if i ∈ names then true else LinearRows.isLinear i p)) =
        (LinearRows.isLinear i p && LinearBlock.allLinear names p)
      by_cases hin : i ∈ names
      · rw [if_pos hin]
        by_cases hall : LinearBlock.allLinear names p = true
        · have hi := (LinearBlockProof.exactBlockTest names p).mp hall i hin
          simp [hall, hi]
        · have hf : LinearBlock.allLinear names p = false := Bool.eq_false_iff.mpr hall
          simp [hf]
      · rw [if_neg hin, Bool.and_comm]

theorem eliminate_bindAll (names : List Nat) (p : Formula) :
    QuantifiedLinear.eliminate (bindAll names (.matrix p)) = LinearBlock.eliminate names p := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      change LinearRows.eliminate i (QuantifiedLinear.eliminate (bindAll names (.matrix p))) = _
      rw [ih]
      rfl

theorem existingBlockCompatibility : QuantifiedLinearTargets.ExistingBlockCompatibility :=
  ⟨admissible_bindAll, eliminate_bindAll⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
