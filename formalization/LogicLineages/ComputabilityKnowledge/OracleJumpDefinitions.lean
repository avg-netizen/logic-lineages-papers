module

public import LogicLineages.ComputabilityKnowledge.OracleUniversalDefinitions

@[expose] public section
/-! Genuine halting characteristics for the checked numeric oracle-program
model. Ordinary Code numbering is the actual Denumerable bijection, so no
ordinary natural index is malformed. Oracle AST malformed indices still
diverge by the separate universal-evaluation theorem. -/
namespace LogicLineages.ComputabilityKnowledge.OracleJump
open OracleProgram OracleUniversal

noncomputable def jump (g : Nat → Nat) (query : Nat) : Nat := by
  classical
  exact if (universal g query).Dom then 1 else 0

def zeroOracle : Nat → Nat := fun _ => 0
noncomputable def firstJump : Nat → Nat := jump zeroOracle
noncomputable def secondJump : Nat → Nat := jump firstJump

def ordinaryHalting (query : Nat) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code query.unpair.1) query.unpair.2).Dom

noncomputable def ordinaryIndicator (query : Nat) : Nat := by
  classical
  exact if ordinaryHalting query then 1 else 0

def ordinaryToFirst (query : Nat) : Nat :=
  Nat.pair (tagged 0 query.unpair.1) query.unpair.2

def firstToOrdinary (compiler : Nat.Partrec.Code) (query : Nat) : Nat :=
  Nat.pair (Encodable.encode compiler) query

end LogicLineages.ComputabilityKnowledge.OracleJump
