module

public import LogicLineages.ComputabilityKnowledge.OracleUniversalDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleUniversalTargets
open OracleProgram OracleDecoder OracleUniversal

def RelativeCertificateTest : Prop :=
  ∀ g : Nat → Nat, ComputableIn {fun n => Part.some (g n)} (certificateTest g)

def RelativeUniversalEvaluation : Prop :=
  ∀ g : Nat → Nat, RecursiveIn {fun n => Part.some (g n)} (universal g)

def EncodedUniversalSemantics : Prop :=
  ∀ (g : Nat → Nat) (p : Program) (input output : Nat),
    output ∈ universal g (Nat.pair (encode p) input) ↔
      output ∈ eval (fun n => Part.some (g n)) p input

def MalformedUniversalDivergence : Prop :=
  ∀ (g : Nat → Nat) (index input : Nat), decode index = none →
    universal g (Nat.pair index input) = Part.none

def DecodedUniversalCalibration : Prop :=
  ∀ (g : Nat → Nat) (query : Nat), universal g query = decodedEvaluation g query

end LogicLineages.ComputabilityKnowledge.OracleUniversalTargets
