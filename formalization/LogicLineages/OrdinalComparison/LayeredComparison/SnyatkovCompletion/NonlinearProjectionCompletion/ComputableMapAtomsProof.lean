module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsAssemblyProof
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
open ComputableMapAtoms
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem value_computable (α : Type) [Primcodable α] (op : α → Nat → Nat)
    (hop : Computable₂ op) : Computable (value op) := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph (Call α) Nat children (assemble op)
    (fun p => p.2) children_primitive.to_comp (assemble_computable hop) Computable.snd
    (value op) children_decreasing (equation op)).2
#print axioms value_computable

theorem actualJointMapProgram : ComputableMapAtomsTargets.ActualJointMapProgram := by
  intro α _ op hop
  change Computable (fun p : α × Nat => LinearRows.Code.mapAtoms (op p.1) p.2)
  exact value_computable α op hop
#print axioms actualJointMapProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsProof
