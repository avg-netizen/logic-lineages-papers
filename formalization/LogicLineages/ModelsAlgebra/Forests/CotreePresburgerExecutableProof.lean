module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutableTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.Proof
open FirstOrder Language RankedParse ProfileAutomatonEncoding CotreePresburger
open CotreePresburgerBoolean CotreePresburgerProduct CotreePresburgerTransition

theorem queryExact : Targets.QueryExact := by
  intro Q _ _ A R q counts
  have hop : (∃ o, Formula.Realize (A.node o q) counts) ↔
      Formula.Realize (A.node .union q) counts ∨ Formula.Realize (A.node .join q) counts := by
    constructor
    · rintro ⟨o,h⟩
      cases o with
      | union => exact Or.inl h
      | join => exact Or.inr h
    · rintro (h|h)
      · exact ⟨.union,h⟩
      · exact ⟨.join,h⟩
  have harity : (0 < ∑ s, counts s ∧ (∑ s, counts s) ≠ 1) ↔ 2 ≤ ∑ s, counts s := by omega
  simp [query, harity, hop, and_assoc]

theorem enabledExact : Targets.EnabledExact := by
  intro Q _ _ A R q
  rw [enabled, CotreePresburgerFiniteDecision.StatementChecks.orderedExact]
  constructor
  · rintro ⟨counts,hc⟩
    rcases (queryExact Q A R q counts).mp hc with ⟨⟨o,h⟩,ha,hz⟩
    exact ⟨o,counts,h,ha,hz⟩
  · rintro ⟨o,counts,h,ha,hz⟩
    exact ⟨counts,(queryExact Q A R q counts).mpr ⟨⟨o,h⟩,ha,hz⟩⟩

theorem step_exact {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) (R : Finset Q) :
    step A R = CotreePresburgerProductive.step A R := by
  ext q
  simp only [step, CotreePresburgerProductive.step, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [enabledExact Q A R q]

theorem reachableExact : Targets.ReachableExact := by
  intro Q _ _ A n
  induction n with
  | zero => rfl
  | succ n ih => simp only [reachable, CotreePresburgerProductive.reachable, ih, step_exact]

theorem productive_eq {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) :
    productive A = CotreePresburgerProductive.productive A := reachableExact Q A _

theorem productiveExact : Targets.ProductiveExact := by
  intro Q _ _ A q
  rw [productive_eq]
  exact CotreePresburgerProductive.StatementChecks.runProductiveExact Q A q

theorem noAcceptingRun_iff {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) :
    noAcceptingRun A = true ↔ ∀ q ∈ productive A, A.accept q = false := by
  simp only [noAcceptingRun, List.all_eq_true, decide_eq_true_eq,
    CotreePresburger.Proof.mem_elements, true_implies]

theorem sourceEmptyExact : Targets.SourceEmptyExact := by
  intro M N _ _
  rw [noAcceptingRun_iff, productive_eq]
  exact (CotreePresburgerProductive.StatementChecks.sourceDifferenceEmptyExact M N).symm

theorem sourceInclusionExact : Targets.SourceInclusionExact := by
  intro M N _ _
  rw [inclusion, sourceEmptyExact]
  exact (CotreePresburgerProduct.StatementChecks.sourceInclusionToEmpty M N).symm
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.Proof
