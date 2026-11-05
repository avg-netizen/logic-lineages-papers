module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
open NormalForm PlainBranchProvenance

theorem mem_nonlinear (p : Formula) (s : Summand) :
    s ∈ nonlinearOccurrences p ↔ s ∈ LinearBlock.occurrences p ∧ nonlinear s = true :=
  List.mem_filter

theorem nonlinear_conjunction (p q : Formula) :
    nonlinearOccurrences (.conjunction p q) = nonlinearOccurrences p ++ nonlinearOccurrences q := by
  simp only [nonlinearOccurrences, LinearBlock.occurrences, LinearRows.atoms,
    List.flatMap_append, List.filter_append]

theorem nonlinear_disjunction (p q : Formula) :
    nonlinearOccurrences (.disjunction p q) = nonlinearOccurrences p ++ nonlinearOccurrences q := by
  simp only [nonlinearOccurrences, LinearBlock.occurrences, LinearRows.atoms,
    List.flatMap_append, List.filter_append]

theorem mem_atom (a : Atom) (s : Summand) :
    s ∈ LinearBlock.occurrences (.atom a) ↔ ∃ b ∈ a.row.2, b.2 = s := by
  simp only [LinearBlock.occurrences, LinearRows.atoms, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_map]

theorem exactLinearityDetection : PlainBranchProvenanceTargets.ExactLinearityDetection := by
  intro i p
  rw [LinearBlockProof.isLinear_iff_occurrences]
  constructor
  · intro h s hs hi
    obtain ⟨hs, hn⟩ := (mem_nonlinear p s).mp hs
    have he := h s hs hi
    rw [he] at hn
    cases hn
  · intro h s hs hi
    by_cases hn : nonlinear s = true
    · exact False.elim (h s ((mem_nonlinear p s).mpr ⟨hs, hn⟩) hi)
    · cases s <;> simp_all [nonlinear, Summand.name]

theorem exactPlainDetection : PlainBranchProvenanceTargets.ExactPlainDetection := by
  intro p
  constructor
  · intro hp s hs
    obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
    have h := List.all_eq_true.mp (List.all_eq_true.mp hp a ha) b hb
    exact h
  · intro hp
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    have h := hp b.2 (List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
    exact h

theorem allLinear_noNonlinear (p : Formula) (h : ∀ i, LinearRows.isLinear i p = true) :
    nonlinearOccurrences p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  exact ((exactLinearityDetection s.name p).mp (h s.name) s hs) rfl

theorem linearGuards : PlainBranchProvenanceTargets.LinearGuards :=
  fun inputs g => allLinear_noNonlinear _ (ShiftedInputGuardsProof.literalGuardLinearity inputs g)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
