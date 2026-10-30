module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations

@[expose] public section

/-! Literal numerical implementation of the source N2 constructor. The only
coefficient multiplication is by the natural constant 2^c(F). Exponent keys
are formed with the already specified removal/addition/height code operations;
equal numeric canonical keys are merged by the actual list algorithm.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCode

open ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormCodeOperations

def exponentialProductCode (d h a b : Nat) : Nat :=
  match h with
  | 0 => Encodable.encode (normalizeMap d
      [(removeCode d 0 a,
        coeffScale d (2 ^ constantCoefficientCode d 0 a) (parseCoefficients b))])
  | h + 1 => Encodable.encode (normalizeMap d
      ((canonicalEntries d (h + 1) b).map (fun e =>
        (addCode d (h + 1) (removeCode d (h + 1) a) (raiseCode d h e.1),
          coeffScale d (2 ^ constantCoefficientCode d (h + 1) a) e.2))))

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCode
