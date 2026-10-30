module

public import LogicLineages.ComputabilityKnowledge.OraclePiThreeDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionLearning

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRecursivePiThree
open OraclePiThree

/-- The last universal coordinate encodes (matrix input z, observation fuel t).
For partial codes this means only absence of an observed zero output. -/
def observationMatrix (code : Nat.Partrec.Code) (a : Nat × Nat × Nat × Nat) : Bool :=
  decide (Nat.Partrec.Code.evaln a.2.2.2.unpair.2 code
    (Encodable.encode (a.1, a.2.1, a.2.2.1, a.2.2.2.unpair.1)) ≠ some 0)

/-- One fixed primitive-recursive matrix, parameterized by the actual ordinary
code index and original matrix parameter in its first numeric coordinate. -/
def codedObservation (a : Nat × Nat × Nat × Nat) : Bool :=
  observationMatrix (Denumerable.ofNat Nat.Partrec.Code a.1.unpair.1)
    (a.1.unpair.2, a.2.1, a.2.2.1, a.2.2.2)

end LogicLineages.ComputabilityKnowledge.OracleRecursivePiThree
