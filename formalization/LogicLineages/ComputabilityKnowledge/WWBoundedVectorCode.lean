module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCode
public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorPadding

@[expose] public section

/-! Actual uniform code construction of the three original source vectors.
The guards use the existing exact positive-expression depth parser; invalid
inputs and depth greater than two are rejected before construction. -/
namespace LogicLineages.ComputabilityKnowledge.WWBoundedVectorCode

open PositiveExpression WWBoundedVectorPadding

abbrev Output := List (List Nat) × List (List Nat) × List (List Nat)

def remainderCode (a b : List Nat) : List Nat := 2 :: (2 :: (a ++ b) ++ [0])

def assemble (a b g : List Nat) : Output :=
  let h := 6 :: (remainderCode a b ++ g)
  ([h, 2 :: (b ++ [0])], [h, a], [2 :: (h ++ [0]), a])

def withinDepth (a b : Nat) : Bool := decide (a ≤ 2) && decide (b ≤ 2)

def paddingCode (d : Nat) (a b : List Nat) : Option Output := do
  let da ← ExponentialNormalizerProgram.depthCode d a
  let db ← ExponentialNormalizerProgram.depthCode d b
  if withinDepth da db then
    let g ← FiniteDepthEnvelope.envelopeCode d (remainderCode a b)
    some (assemble a b g)
  else none

def sourceOutput {d : Nat} (u v : Expr (Fin d)) : Output :=
  ((left u v).map WWOrdinalPrefixCode.encode,
    (weakRight u v).map WWOrdinalPrefixCode.encode,
    (strictRight u v).map WWOrdinalPrefixCode.encode)

end LogicLineages.ComputabilityKnowledge.WWBoundedVectorCode
