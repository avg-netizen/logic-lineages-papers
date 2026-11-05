module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceBooleanGraph

private theorem rows_plain (t : BaseTerm) : ∀ s row, row ∈ rows s t →
    PlainPhiDominance.isPlain row = true := by
  induction t with
  | numeral n =>
      intro s row hr
      simp only [rows, List.mem_singleton] at hr
      subst row
      rfl
  | «variable» i =>
      intro s row hr
      simp only [rows, List.mem_singleton] at hr
      subst row
      rfl
  | add a b iha ihb =>
      intro s row hr
      simp only [rows, List.mem_append, List.mem_singleton] at hr
      rcases hr with (ha | hb) | hr
      · exact iha s row ha
      · exact ihb (s + nodeCount a) row hb
      · subst row; rfl
  | phi a ih =>
      intro s row hr
      simp only [rows, List.mem_append, List.mem_singleton] at hr
      rcases hr with ha | hr
      · exact ih s row ha
      · subst row; rfl

private theorem equation_plain (row : Row) :
    MaximalPlainBranch.isPlain (equation row) = PlainPhiDominance.isPlain row := by
  simp [MaximalPlainBranch.isPlain, LinearRows.atoms, equation, Atom.row,
    PlainPhiDominance.isPlain, negateRow, List.all_map]

private theorem equations_plain (rs : List Row) (h : ∀ row ∈ rs, PlainPhiDominance.isPlain row = true) :
    MaximalPlainBranch.isPlain (equations rs) = true := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
      have hr := (equation_plain row).trans (h row (List.mem_cons_self ..))
      have hs := ih (fun r hm => h r (List.mem_cons_of_mem _ hm))
      simpa only [equations, List.foldr_cons, MaximalPlainBranch.isPlain, LinearRows.atoms,
        List.all_append] using Bool.and_eq_true_iff.mpr ⟨hr, hs⟩

theorem graph_plain (s : Nat) (t : BaseTerm) : MaximalPlainBranch.isPlain (graph s t) = true :=
  equations_plain (rows s t) (rows_plain t s)

private theorem relation_plain (strict : Bool) (x y : Nat) :
    MaximalPlainBranch.isPlain (SourceRows.relation strict x y) = true := by
  cases strict <;> simp [SourceRows.relation, SourceRows.strictRow, equation, negateRow, variableRow,
    MaximalPlainBranch.isPlain, LinearRows.atoms, Atom.row, PlainPhiDominance.isPlain]

theorem predicate_plain (p : SourceFormula) : ∀ s, MaximalPlainBranch.isPlain (predicate s p) = true := by
  induction p with
  | equal a b => intro s; exact relation_plain false _ _
  | less a b => intro s; exact relation_plain true _ _
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      intro s
      simpa only [predicate, MaximalPlainBranch.isPlain, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨ihp s, ihq (s + nodeCount (forest p))⟩
  | existsNat i p ih => intro s; rfl

theorem plainCompiledMatrix : SourceBooleanGraphTargets.PlainCompiledMatrix := by
  intro p s
  simpa only [matrix, MaximalPlainBranch.isPlain, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨graph_plain s (forest p), predicate_plain p s⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
