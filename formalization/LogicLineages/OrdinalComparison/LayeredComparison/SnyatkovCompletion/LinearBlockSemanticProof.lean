module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockOccurrencesProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
open NormalForm

theorem isLinear_iff_occurrences (i : Nat) (p : Formula) :
    LinearRows.isLinear i p = true ↔
      ∀ s ∈ LinearBlock.occurrences p, s.name = i → s = Summand.variable i := by
  rw [LinearRowsSemanticProof.exactLinearityTest i p]
  constructor
  · intro h s hs hi
    obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
    exact h a ha w hw hi
  · intro h a ha w hw hi
    apply h w.2
    · exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
    · exact hi

theorem exactLinearityAfterElimination : LinearBlockTargets.ExactLinearityAfterElimination := by
  intro i j p
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    apply (isLinear_iff_occurrences i (LinearRows.eliminate i p)).mpr
    intro s hs hi
    exact False.elim (((exactOneNameOccurrences i p s).mp hs).1 hi)
  · rw [if_neg hji]
    apply Bool.eq_iff_iff.mpr
    change LinearRows.isLinear j (LinearRows.eliminate i p) = true ↔
      LinearRows.isLinear j p = true
    rw [isLinear_iff_occurrences, isLinear_iff_occurrences]
    constructor
    · intro h s hs hj
      apply h s
      · exact (exactOneNameOccurrences i p s).mpr ⟨by simpa only [hj] using hji, hs⟩
      · exact hj
    · intro h s hs hj
      exact h s ((exactOneNameOccurrences i p s).mp hs).2 hj

theorem exactBlockTest : LinearBlockTargets.ExactBlockTest := by
  intro names p
  simp only [LinearBlock.allLinear, List.all_eq_true]

theorem eliminate_preserves_linearity (names : List Nat) (p : Formula) (i : Nat)
    (h : LinearRows.isLinear i p = true) :
    LinearRows.isLinear i (LinearBlock.eliminate names p) = true := by
  induction names with
  | nil => exact h
  | cons j names ih =>
      change LinearRows.isLinear i (LinearRows.eliminate j (LinearBlock.eliminate names p)) = true
      rw [exactLinearityAfterElimination j i (LinearBlock.eliminate names p)]
      split_ifs
      · rfl
      · exact ih

theorem actualBlockElimination : LinearBlockTargets.ActualBlockElimination := by
  intro names p
  induction names with
  | nil => intro _ ν; rfl
  | cons i names ih =>
      intro h ν
      have hall := (exactBlockTest (i :: names) p).mp h
      have hi := hall i List.mem_cons_self
      have hrest : LinearBlock.allLinear names p = true :=
        (exactBlockTest names p).mpr (fun j hj => hall j (List.mem_cons_of_mem i hj))
      change (LinearRows.eliminate i (LinearBlock.eliminate names p)).eval ν ↔
        ∃ n : Nat, existsPrefix (Function.update ν i n) names p
      rw [LinearRowsSemanticProof.actualLinearElimination i (LinearBlock.eliminate names p)
        (eliminate_preserves_linearity names p i hi) ν]
      exact exists_congr (fun n => ih hrest (Function.update ν i n))

theorem exactBlockOccurrences : LinearBlockTargets.ExactBlockOccurrences := by
  intro names p s
  induction names with
  | nil => simp [LinearBlock.eliminate]
  | cons i names ih =>
      change s ∈ LinearBlock.occurrences
        (LinearRows.eliminate i (LinearBlock.eliminate names p)) ↔ _
      rw [exactOneNameOccurrences i (LinearBlock.eliminate names p) s, ih]
      simp only [List.mem_cons, not_or]
      tauto

theorem exactBlockSupport : LinearBlockTargets.ExactBlockSupport := by
  intro names p v
  induction names with
  | nil => simp [LinearBlock.eliminate]
  | cons i names ih =>
      change v ∈ (LinearRows.eliminate i (LinearBlock.eliminate names p)).variables ↔ _
      rw [LinearRowsSupportProof.exactOutputSupport i (LinearBlock.eliminate names p) v, ih]
      simp only [List.mem_cons, not_or]
      tauto

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
