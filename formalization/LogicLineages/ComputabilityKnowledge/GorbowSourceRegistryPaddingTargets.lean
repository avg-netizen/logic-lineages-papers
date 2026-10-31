module

public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.Targets
open GorbowPRProgram GorbowPRRegistry List.Vector

def Layout : Prop := ∀ pF pR : Program 1,
  nodes (root pF pR) = paddingPrefix pF pR ++ nodes pF ++ middle pR ++ nodes pR ++ [⟨4,dummy⟩]

def FunctionRoot : Prop := ∀ pF pR : Program 1,
  (nodes (root pF pR))[functionTag]? = some ⟨1,pF⟩

def RelationRoot : Prop := ∀ pF pR : Program 1,
  (nodes (root pF pR))[relationTag pF]? = some ⟨1,pR⟩

def LowTagsHighArity : Prop := ∀ (pF pR : Program 1) (tag : Nat) (a : Packed),
  tag ≤ 4 → (nodes (root pF pR))[tag]? = some a → 4 ≤ a.1

def HeaderDisjoint : Prop := ∀ (pF pR : Program 1) (tag : Nat) (a : Packed),
  (nodes (root pF pR))[tag]? = some a →
    ∀ name ∈ functionNames, (a.1,tag) ≠ name

def SpecificPrograms : Prop :=
  Primrec sourceFunction ∧ Primrec sourceRelationValue ∧
    ∃ pF pR : Program 1,
      (∀ x, evaluate pF (x ::ᵥ List.Vector.nil) = sourceFunction x) ∧
      (∀ x, evaluate pR (x ::ᵥ List.Vector.nil) = sourceRelationValue x)

end LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding.Targets
