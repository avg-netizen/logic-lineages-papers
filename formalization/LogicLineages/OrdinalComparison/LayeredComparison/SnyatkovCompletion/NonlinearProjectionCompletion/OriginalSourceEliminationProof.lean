module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationBinderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
open OriginalSourceElimination

theorem hFreeSourceOutput : OriginalSourceEliminationTargets.HFreeSourceOutput := by
  intro p
  induction p with
  | equal a b =>
      exact Bool.and_eq_true_iff.mpr ⟨(literalBaseEmbedding a).2.2, (literalBaseEmbedding b).2.2⟩
  | less a b =>
      exact Bool.and_eq_true_iff.mpr ⟨(literalBaseEmbedding a).2.2, (literalBaseEmbedding b).2.2⟩
  | negative p ih => exact ih
  | conjunction p q ihp ihq => exact Bool.and_eq_true_iff.mpr ⟨ihp, ihq⟩
  | existsNat i p ih => exact hFreeBinderOutput i (eliminate p) ih

theorem actualSourceElimination : OriginalSourceEliminationTargets.ActualSourceElimination := by
  intro p
  induction p with
  | equal a b =>
      intro ν
      change ((embed a).value ν = (embed b).value ν ↔ a.value ν = b.value ν)
      rw [(literalBaseEmbedding a).1 ν, (literalBaseEmbedding b).1 ν]
  | less a b =>
      intro ν
      change ((embed a).value ν < (embed b).value ν ↔ a.value ν < b.value ν)
      rw [(literalBaseEmbedding a).1 ν, (literalBaseEmbedding b).1 ν]
  | negative p ih =>
      intro ν
      exact not_congr (ih ν)
  | conjunction p q ihp ihq =>
      intro ν
      exact and_congr (ihp ν) (ihq ν)
  | existsNat i p ih =>
      intro ν
      exact (actualBinderElimination i (eliminate p) (hFreeSourceOutput p) ν).trans
        (exists_congr fun n => ih (Function.update ν i n))

theorem originalSourceNameSupport : OriginalSourceEliminationTargets.OriginalSourceNameSupport := by
  intro p
  induction p with
  | equal a b =>
      intro i hi
      simpa only [eliminate, Matrix.variables, SourceFormula.variables,
        (literalBaseEmbedding a).2.1, (literalBaseEmbedding b).2.1] using hi
  | less a b =>
      intro i hi
      simpa only [eliminate, Matrix.variables, SourceFormula.variables,
        (literalBaseEmbedding a).2.1, (literalBaseEmbedding b).2.1] using hi
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      intro i hi
      rcases List.mem_append.mp hi with hp | hq
      · exact List.mem_append_left _ (ihp i hp)
      · exact List.mem_append_right _ (ihq i hq)
  | existsNat i p ih =>
      intro j hj
      have h := originalBinderNameSupport i (eliminate p) (hFreeSourceOutput p) j hj
      apply List.mem_filter.mpr
      exact ⟨ih j h.2, by simpa using h.1⟩

#print axioms hFreeSourceOutput
#print axioms actualSourceElimination
#print axioms originalSourceNameSupport
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
