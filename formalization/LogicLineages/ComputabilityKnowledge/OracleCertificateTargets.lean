module

public import LogicLineages.ComputabilityKnowledge.OracleCertificateDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleCertificateTargets
open OracleProgram OracleDerivation OracleCertificate

def CertificatePacking : Prop :=
  ∀ (code input output fuel : Nat) (children : List Nat),
    let i := packNode code input output fuel children
    0 < i ∧ nodeCode i = code ∧ nodeInput i = input ∧ nodeOutput i = output ∧
      nodeFuel i = fuel ∧ nodeChildren i = some children ∧ ∀ child ∈ children, child < i

def PrimitiveRecursiveCertificateStep : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => certificateStep z.1 z.2.1 z.2.2)

def RelativeCertificateVerifier : Prop :=
  ∀ g : Nat → Nat, ComputableIn {fun n => Part.some (g n)} (certificateFlag g)

def NumericCertificateSound : Prop :=
  ∀ (g : Nat → Nat) (i : Nat), validCertificate g i = true →
    ∃ p : Program, encode p = nodeCode i ∧ Derives g p (nodeInput i) (nodeOutput i)

def NumericCertificateComplete : Prop :=
  ∀ (g : Nat → Nat) (p : Program) (input output : Nat), Derives g p input output →
    ∃ i : Nat, validCertificate g i = true ∧ nodeCode i = encode p ∧
      nodeInput i = input ∧ nodeOutput i = output

end LogicLineages.ComputabilityKnowledge.OracleCertificateTargets
