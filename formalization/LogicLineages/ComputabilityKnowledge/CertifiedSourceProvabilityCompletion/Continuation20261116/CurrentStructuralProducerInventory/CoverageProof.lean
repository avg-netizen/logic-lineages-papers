module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CoverageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
variable {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)

theorem root {n : Nat} (q : Program n) (entry : Packed)
 (h : entry ∈ localItems installed lhs rhs t old a baseX q) :
 entry ∈ inventory installed lhs rhs t old a baseX q := by
 cases q <;> simp only [inventory, List.mem_append] <;> tauto

theorem occurrence {n : Nat} {q : Program n} {u : Packed} (h : Occurs u q)
 (entry : Packed) (he : entry ∈ localItems installed lhs rhs t old a baseX u.2) :
 entry ∈ inventory installed lhs rhs t old a baseX q := by
 induction h with
 | here q h =>
  subst u
  exact root installed lhs rhs t old a baseX q entry he
 | compositionFunction f g _ ih =>
  simp only [inventory,List.mem_append]
  tauto
 | compositionArgument f g i _ ih =>
  have hg : entry ∈ (List.ofFn (fun j => inventory installed lhs rhs t old a baseX (g j))).flatten := List.mem_flatten.mpr ⟨inventory installed lhs rhs t old a baseX (g i), List.mem_ofFn.mpr ⟨i,rfl⟩,ih⟩
  simp only [inventory,List.mem_append]
  tauto
 | recursionBase f g _ ih =>
  simp only [inventory,List.mem_append]
  tauto
 | recursionStep f g _ ih =>
  simp only [inventory,List.mem_append]
  tauto

theorem evaluator {n : Nat} (q : Program n) :
 (⟨n,q⟩ : Packed) ∈ localItems installed lhs rhs t old a baseX q := by
 simp only [localItems,List.mem_append,List.mem_cons,List.mem_singleton]
 tauto

theorem compiled {n : Nat} (q : Program n) :
 (⟨n+1,CurrentStructuralProducerCompiler.compile q⟩ : Packed) ∈ localItems installed lhs rhs t old a baseX q := by
 simp only [localItems,List.mem_append,List.mem_cons,List.mem_singleton]
 tauto

theorem extended {m : Nat} (f : Program m) (g : Program (m+2)) :
 (⟨6,CurrentRecursionProducerSource.extendedExtra installed lhs rhs t old a baseX
  f g (CurrentStructuralProducerCompiler.compile f) (CurrentStructuralProducerCompiler.compile g)⟩ : Packed) ∈
 localItems installed lhs rhs t old a baseX (.recursion f g) := by
 simp only [localItems,List.mem_append,List.mem_cons,List.mem_singleton]
 tauto

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CoverageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CoverageProof
