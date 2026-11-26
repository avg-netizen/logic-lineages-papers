module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeGraphAssemblyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem graph_computable : Computable₂ graph := by
  classical
  change Computable (fun p : GraphCall => graph p.1 p.2)
  exact (FiniteGraph.Proof.exactDecreasingGraph GraphCall Nat graphChildren graphAssemble
    (fun p => p.2) graphChildren_computable graphAssemble_computable Computable.snd
    (fun p => graph p.1 p.2) graphChildren_decreasing graph_equation).2
#print axioms graph_computable

theorem actualGraphPrograms : ExpandedGraphCodeTargets.ActualGraphPrograms :=
  ⟨multiplyRow_primitive.to_comp, subtraction_primitive.to_comp,
    division_primitive.to_comp, inverse_primitive.to_comp, graph_computable⟩
#print axioms actualGraphPrograms


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
