module

public import LogicLineages.ComputabilityKnowledge.GorbowPACore

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowPACore
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPACore

def WeakeningRealization : Prop := ∀ (n : Nat) (φ : Formula n) (I : Interpretation) (v : Fin n → Nat) (x : Nat),
  (weaken φ).realize I (Fin.cases x v) ↔ φ.realize I v

def LogicalSoundness : Prop := ∀ (n : Nat) (w : LogicalInstance n) (I : Interpretation) (v : Fin n → Nat),
  (logicalFormula w).realize I v

def ArithmeticSoundness : Prop := ∀ (n : Nat) (w : ArithmeticInstance n) (I : Interpretation) (v : Fin n → Nat),
  (arithmeticFormula w).realize I v

def InductionCalibration : Prop := ∀ (n : Nat) (φ : Formula (n+1)),
  arithmeticFormula (.induction φ) = GorbowStandardInduction.inductionAxiom φ

def ProofSoundness : Prop := ∀ (n : Nat) (φ : Formula n) (p : Proof φ) (I : Interpretation) (v : Fin n → Nat),
  φ.realize I v

def Target : Prop := WeakeningRealization ∧ LogicalSoundness ∧ ArithmeticSoundness ∧ InductionCalibration ∧ ProofSoundness
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowPACore
