module

public import LogicLineages.ComputabilityKnowledge.RayCodeEvaluation

@[expose] public section

/-! Exact all-raw-code numeric evaluator supplier for source paper02 lem:ray.
There is no canonical-code premise concealing aggregation or a computability
oracle. Uniform effectivity is about the explicit program just defined. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayCodeEvaluation

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open LogicLineages.ComputabilityKnowledge.RayCodeEvaluation

def LiteralAffineEvaluation : Prop :=
  ∀ (d : Nat) (c : CoeffCode) (xs : List Nat),
    affineEval d c xs = affineValue (coeffDecode d c) (fun i => xs.getD i.val 0)

def LiteralHereditaryEvaluation : Prop :=
  ∀ (d h n : Nat) (xs : List Nat),
    evalCode d h n xs = value h (formDecode d h n) (fun i => xs.getD i.val 0)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × CoeffCode × List Nat => affineEval p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × List Nat => evalCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := LiteralAffineEvaluation ∧ LiteralHereditaryEvaluation ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.RayCodeEvaluation
