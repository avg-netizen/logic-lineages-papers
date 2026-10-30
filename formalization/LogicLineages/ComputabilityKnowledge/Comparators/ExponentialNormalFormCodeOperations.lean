module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizer

@[expose] public section

/-! Exact implementation supplier: all code operations must commute with
the already fixed mathematical map operations, on every raw input code.
Their actual uniform primitive-recursive graphs are additional conclusions.
The code for E and the complete literal syntax compiler remain separate.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodeOperations

open ExponentialNormalForm ExponentialHereditaryCodec
open ExponentialNormalFormProduct ExponentialNormalizer
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations

def Variables : Prop :=
  ∀ (d h : Nat) (i : Fin d),
    CodeCanonical d h (variableCode d h i.val) ∧
    formDecode d h (variableCode d h i.val) = variableForm h i

def Addition : Prop :=
  ∀ (d h a b : Nat),
    CodeCanonical d h (addCode d h a b) ∧
    formDecode d h (addCode d h a b) =
      addForm h (formDecode d h a) (formDecode d h b)

def ConstantRemoval : Prop :=
  ∀ (d h n : Nat),
    constantCoefficientCode d h n = constantCoefficient h (formDecode d h n) ∧
    CodeCanonical d h (removeCode d h n) ∧
    formDecode d h (removeCode d h n) = removeConstant h (formDecode d h n)

def HeightTransport : Prop :=
  ∀ (d h n : Nat),
    CodeCanonical d (h + 1) (raiseCode d h n) ∧
    formDecode d (h + 1) (raiseCode d h n) = raiseForm h (formDecode d h n)

def ActualPrimitiveRecursion : Prop :=
  Primrec (fun p : Nat × Nat × Nat => variableCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => addCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => constantCoefficientCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => removeCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => raiseCode p.1 p.2.1 p.2.2)

def Target : Prop := Variables ∧ Addition ∧ ConstantRemoval ∧
  HeightTransport ∧ ActualPrimitiveRecursion

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodeOperations
