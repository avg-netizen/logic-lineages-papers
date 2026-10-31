module

public import LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormTargets
open OracleThirdJumpNormalForm OracleCertificate OracleUniversal OracleJump OraclePiThree

def FiniteOracleAgreement : Prop :=
  ∀ (g h : Nat → Nat) (c : Nat),
    (∀ j ≤ c, g (nodeInput j) = h (nodeInput j)) →
    validCertificate g c = validCertificate h c

def ActualHaltingCertificate : Prop :=
  ∀ (g : Nat → Nat) (q : Nat),
    (universal g q).Dom ↔ ∃ c, certificateTest g (Nat.pair q c) = 0

def ExplicitMatricesPrimitiveRecursive : Prop :=
  Primrec (fun a : Nat × Nat => firstMatrix a.1 a.2) ∧
  Primrec (fun a : Nat × Nat × Nat => secondMatrix a.1 a.2.1 a.2.2) ∧
  Primrec thirdComplementMatrix

def ActualFirstJumpNormalForm : Prop :=
  ∀ q, firstJump q = 1 ↔ ∃ c, firstMatrix q c = true

def ActualSecondJumpNormalForm : Prop :=
  ∀ q, secondJump q = 1 ↔ ∃ w, ∀ y, secondMatrix q w y = true

def ActualThirdJumpNormalForm : Prop :=
  ∀ q, thirdJump q = 1 ↔ ∃ w, ∀ y, ∃ z, thirdMatrix q w y z = true

def ActualThirdJumpComplement : Prop :=
  ∀ q, thirdJump q = 0 ↔ ∀ w, ∃ y, ∀ z, thirdComplementMatrix (q, w, y, z) = true

def RecursiveActualThirdJumpComplement : Prop :=
  ∃ R : OraclePiThree.Matrix, Computable R ∧
    ∀ q, (∀ x, ∃ y, ∀ z, R (q, x, y, z) = true) ↔ thirdJump q = 0

end LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormTargets
