module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountsTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.Proof
open CotreePresburger

@[simp] theorem count_chunks {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → List β) (b : β) :
    (xs.flatMap f).count b = (xs.map (fun a => (f a).count b)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem sum_elements {α : Type} [Fintype α] [LinearOrder α] (f : α → Nat) :
    ((elements α).map f).sum = ∑ a, f a := by
  rw [elements, ← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp

theorem wordCountsExact : Targets.WordCountsExact := by
  intro Q _ _ counts B
  rw [wordOfCounts, count_chunks, sum_elements]
  calc
    _ = ∑ C : Finset Q, (List.replicate (counts C) C).count B :=
      Equiv.sum_comp ofColex _
    _ = counts B := by simp [List.count_replicate, beq_iff_eq]

theorem formulaCountsExact : Targets.FormulaCountsExact := by
  intro Q _ _ δ root counts
  have hcount : (fun B => (wordOfCounts counts).count B) = counts :=
    funext (wordCountsExact Q counts)
  rw [← hcount, CotreePresburgerGrammar.StatementChecks.formulaGrammarExact]
  constructor
  · rintro ⟨w,hw,hperm⟩
    exact ⟨w,hw,fun B => hperm.count_eq B⟩
  · rintro ⟨w,hw,hcounts⟩
    refine ⟨w,hw,?_⟩
    exact List.perm_iff_count.mpr hcounts

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.Proof
