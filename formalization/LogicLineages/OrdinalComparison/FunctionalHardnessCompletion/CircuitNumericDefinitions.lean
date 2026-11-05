module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitLinearTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open CircuitLinear

/-- Interpret a fixed-width gate record using the literal circuit-to-system
builder. The third branch agrees with the actual multiplication tag 2; behavior
on other tags is irrelevant to the canonical-code calibration below. -/
def gateRecordRows (n g i tag x y : Nat) : List Row :=
  if tag = 0 then gateRows n g i (.constant x)
  else if tag = 1 then gateRows n g i (.add x y)
  else gateRows n g i (.mul x y)

/-- Read the actual circuit codec's consecutive three-cell gate records. The
start index is retained explicitly for the list-induction calibration. -/
def gateCodeRows (n g start : Nat) (code : List Nat) : List Row :=
  (List.range (code.length / 3)).flatMap fun j =>
    gateRecordRows n g (start + j) (code.getD (3*j) 0)
      (code.getD (3*j+1) 0) (code.getD (3*j+2) 0)

/-- The input header is exactly inputCount, leftOutput, rightOutput. Gate count
is obtained from the fixed-width suffix, and all original shared indices and
reserved slots are passed unchanged to the literal row constructors. -/
def systemFromCode (code : List Nat) : SystemCode :=
  let n := code.getD 0 0
  let l := code.getD 1 0
  let r := code.getD 2 0
  let gates := code.drop 3
  let g := gates.length / 3
  (unknownCount n g,
    inputRows n g ++ gateCodeRows n g 0 gates ++
    [[wireMonomial 1 0 l, wireMonomial (-1) 0 r]] ++
    constantRows (scalarCount n g) (constantAux n g))

/-- Only canonical circuit inputs are specified by NumericCircuitEncoder.
This total front end deliberately makes no validity claim for other lists;
the later original-polynomial adapter must perform its own rejection checks.
The output is the global Encodable code of the actual SystemCode, with the
standard Int encoding and no private replacement encoding. -/
def encode (code : List Nat) : Option Nat :=
  some (Encodable.encode (systemFromCode code))

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric
