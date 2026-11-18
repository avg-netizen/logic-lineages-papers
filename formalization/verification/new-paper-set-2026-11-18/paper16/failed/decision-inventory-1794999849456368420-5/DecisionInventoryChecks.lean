import LogicLineages.PersistentMarking.DecisionInventoryProof
import LogicLineages.PersistentMarking.DecisionDepthProof
namespace LogicLineages.PersistentMarking.DecisionInventoryChecks
open Spine NameBridge TypeSupport DecisionInventory

theorem exact_freeInventoryExact : DecisionInventoryTargets.FreeInventoryExact := DecisionInventoryProof.freeExact
theorem exact_auxiliaryContainsLiteral : DecisionInventoryTargets.AuxiliaryContainsLiteral := DecisionInventoryProof.containsLiteral
theorem exact_auxiliaryContainsDeclarations : DecisionInventoryTargets.AuxiliaryContainsDeclarations := DecisionInventoryProof.declarations
theorem exact_ordinaryAuxiliaryExact : DecisionInventoryTargets.OrdinaryAuxiliaryExact := DecisionInventoryProof.ordinaryExact
theorem exact_rankedDeclarationExact : DecisionInventoryTargets.RankedDeclarationExact := DecisionInventoryProof.rankedDeclaration
theorem exact_subtypeClosed : DecisionInventoryTargets.SubtypeClosed := DecisionInventoryProof.auxiliaryClosed
theorem exact_depthExact : DecisionInventoryTargets.DepthExact := DecisionDepthProof.bound
theorem exact_depthAttained : DecisionInventoryTargets.DepthAttained := DecisionDepthProof.attained
theorem exact_inputTypesExact : DecisionInventoryTargets.InputTypesExact := by
  intro Γ Δ s t σ τ hs ht hos hot ρ
  simp only [inventory,List.mem_append,DecisionInventoryProof.ordinaryExact Γ s σ hs hos ρ,DecisionInventoryProof.ordinaryExact Δ t τ ht hot ρ]
#print axioms exact_freeInventoryExact
#print axioms exact_auxiliaryContainsLiteral
#print axioms exact_auxiliaryContainsDeclarations
#print axioms exact_ordinaryAuxiliaryExact
#print axioms exact_rankedDeclarationExact
#print axioms exact_subtypeClosed
#print axioms exact_depthExact
#print axioms exact_depthAttained
#print axioms exact_inputTypesExact
end LogicLineages.PersistentMarking.DecisionInventoryChecks
