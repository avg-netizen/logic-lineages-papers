module

public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec

@[expose] public section

/-! Literal numerical evaluator for the existing hereditary finite-map codes.
Missing variable-list entries are zero, exactly as in the semantic tuple below.
The algorithm does not require canonical inputs: duplicate decoded keys are
summed by formDecode and by the literal numerical row fold. -/
namespace LogicLineages.ComputabilityKnowledge.RayCodeEvaluation

open ExponentialNormalFormCodec ExponentialHereditaryCodec

def affineEval (d : Nat) (c : CoeffCode) (xs : List Nat) : Nat :=
  c.getD 0 0 + (List.range d).foldr
    (fun i acc => c.getD (i + 1) 0 * xs.getD i 0 + acc) 0

def evalCode (d : Nat) : Nat → Nat → List Nat → Nat
  | 0, n, xs => affineEval d (parseCoefficients n) xs
  | h + 1, n, xs => (parseEntries n).foldr
      (fun e acc => affineEval d e.2 xs * 2 ^ evalCode d h e.1 xs + acc) 0

end LogicLineages.ComputabilityKnowledge.RayCodeEvaluation
