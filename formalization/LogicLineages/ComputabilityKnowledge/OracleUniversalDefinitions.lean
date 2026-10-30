module

public import LogicLineages.ComputabilityKnowledge.OracleCertificateDefinitions
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionDefinitions

@[expose] public section
/-! A genuine partial universal evaluator for total oracles, by search over
checked finite certificates. Invalid program indices have no certificate.
No totality of search, uniform oracle-independent syntax index, or jump
calibration is included in these definitions. -/
namespace LogicLineages.ComputabilityKnowledge.OracleUniversal
open OracleProgram OracleDecoder OracleCertificate OracleRelativeRecursion

def certificateTest (g : Nat → Nat) (z : Nat) : Nat :=
  if validCertificate g z.unpair.2 &&
    (nodeCode z.unpair.2 == z.unpair.1.unpair.1) &&
    (nodeInput z.unpair.2 == z.unpair.1.unpair.2) then 0 else 1

def universal (g : Nat → Nat) (query : Nat) : Part Nat :=
  (zeroSearch (certificateTest g) query).map nodeOutput

def decodedEvaluation (g : Nat → Nat) (query : Nat) : Part Nat :=
  match decode query.unpair.1 with
  | none => Part.none
  | some p => eval (fun n => Part.some (g n)) p query.unpair.2

end LogicLineages.ComputabilityKnowledge.OracleUniversal
