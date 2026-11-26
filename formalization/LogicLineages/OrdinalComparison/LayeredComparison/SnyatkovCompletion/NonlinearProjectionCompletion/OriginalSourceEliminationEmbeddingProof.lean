module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
open OriginalSourceElimination CommonLayerSyntax

theorem literalBaseEmbedding : OriginalSourceEliminationTargets.LiteralBaseEmbedding := by
  intro a
  induction a with
  | numeral n => exact ⟨fun _ => rfl, rfl, rfl⟩
  | «variable» i => exact ⟨fun _ => rfl, rfl, rfl⟩
  | add a b iha ihb =>
      refine ⟨?_, ?_, ?_⟩
      · intro ν
        change (embed a).value ν + (embed b).value ν = a.value ν + b.value ν
        rw [iha.1 ν, ihb.1 ν]
      · change (embed a).variables ++ (embed b).variables = a.variables ++ b.variables
        rw [iha.2.1, ihb.2.1]
      · exact Bool.and_eq_true_iff.mpr ⟨iha.2.2, ihb.2.2⟩
  | phi a ih =>
      refine ⟨?_, ih.2.1, ih.2.2⟩
      intro ν
      change Phi ((embed a).value ν) = Phi (a.value ν)
      rw [ih.1 ν]

#print axioms literalBaseEmbedding
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
