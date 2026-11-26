module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationEmbeddingProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
open OriginalSourceElimination

theorem exactBinderBlock : OriginalSourceEliminationTargets.ExactBinderBlock := by
  intro i p
  have h := ExpandedBooleanGraphProof.exactFreshGraphNames [i] p
  apply List.nodup_cons.mpr
  refine ⟨?_, h.1⟩
  intro hi
  exact (h.2 i hi).1 (List.mem_singleton_self i)

theorem literalBinderInputClass : OriginalSourceEliminationTargets.LiteralBinderInputClass := by
  intro i p hp
  exact ExpandedBooleanGraphProof.literalZeroShiftGraphClass [i] p hp

theorem actualBinderElimination : OriginalSourceEliminationTargets.ActualBinderElimination := by
  intro i p hp ν
  have h := WholeBoundInitializationProof.actualInitializedProjection
    (binderBlock i p) (graphFormula i p) (exactBinderBlock i p)
    (literalBinderInputClass i p hp) ν
  change ((eliminateBinder i p).eval ν ↔ ∃ n : Nat,
    NormalForm.existsPrefix (Function.update ν i n) (graphNames i p) (graphFormula i p)) at h
  exact h.trans (exists_congr fun n =>
    ExpandedBooleanGraphProof.actualExpandedMatrixGraph [i] p (Function.update ν i n) hp)

theorem originalBinderNameSupport : OriginalSourceEliminationTargets.OriginalBinderNameSupport := by
  intro i p hp j hj
  have h := WholeBoundInitializationProof.originalProjectedNameSupport
    (binderBlock i p) (graphFormula i p) (exactBinderBlock i p)
    (literalBinderInputClass i p hp) j hj
  refine ⟨?_, ?_⟩
  · intro hji
    subst j
    exact h.1 (List.mem_cons_self)
  · rcases ExpandedBooleanGraphProof.originalGraphNameSupport [i] p j h.2 with hjp | hjg
    · exact hjp
    · exact False.elim (h.1 (List.mem_cons_of_mem i hjg))

theorem hFreeBinderOutput : OriginalSourceEliminationTargets.HFreeBinderOutput := by
  intro i p hp
  exact WholeBoundInitializationProof.hFreeProjectedOutput
    (binderBlock i p) (graphFormula i p) (exactBinderBlock i p)
    (literalBinderInputClass i p hp)

#print axioms exactBinderBlock
#print axioms literalBinderInputClass
#print axioms actualBinderElimination
#print axioms originalBinderNameSupport
#print axioms hFreeBinderOutput
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
