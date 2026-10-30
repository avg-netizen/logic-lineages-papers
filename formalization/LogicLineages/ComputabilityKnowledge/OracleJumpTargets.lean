module

public import LogicLineages.ComputabilityKnowledge.OracleJumpDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleJumpTargets
open OracleUniversal OracleJump

def ActualJumpCharacteristic : Prop :=
  ∀ (g : Nat → Nat) (query : Nat),
    (jump g query = 1 ↔ (universal g query).Dom) ∧
    (jump g query = 0 ↔ ¬(universal g query).Dom)

def ZeroOracleUniversalPartrec : Prop := Partrec (universal zeroOracle)

def OrdinaryToFirstCalibration : Prop :=
  Primrec ordinaryToFirst ∧ ∀ query, firstJump (ordinaryToFirst query) = ordinaryIndicator query

def FirstToOrdinaryCalibration : Prop :=
  ∃ compiler : Nat.Partrec.Code,
    (∀ query, compiler.eval query = universal zeroOracle query) ∧
    Primrec (firstToOrdinary compiler) ∧
    ∀ query, ordinaryIndicator (firstToOrdinary compiler query) = firstJump query

def FirstJumpRelativeEquivalence : Prop :=
  ComputableIn {fun n => Part.some (ordinaryIndicator n)} firstJump ∧
    ComputableIn {fun n => Part.some (firstJump n)} ordinaryIndicator

end LogicLineages.ComputabilityKnowledge.OracleJumpTargets
