module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexTargets
open Cipher CipherIndex

/-- Multiplication by an even number gains a binary congruence bit; AND with
an arbitrary fixed mask preserves that congruence. -/
def EvenMaskedProductFixedPointUnique : Prop := ∀ A B c w x y : Nat,
  2 ∣ c → A+((x*c) &&& w)=x+B → A+((y*c) &&& w)=y+B → x=y

/-- Exact arithmetic characterization of the actual sparse index sum, over
all natural inputs and including the empty sequence. -/
def IndexArithmeticCharacterization : Prop := ∀ n q a : Nat,
  (n+1<q ∧ a=index n q) ↔ IndexEquations n q a

/-- The variable-input graph of the actual sparse index sum on its original
domain, not a premise asserting a Diophantine index supplier. -/
def IndexDiophantine : Prop :=
  Dioph {v : Fin 3 → Nat | v 0+1<v 1 ∧ v 2=index (v 0) (v 1)}

/-- Source CodeNat: valid sparse encoding of the actual function i↦i. -/
def IndexCipherDiophantine : Prop :=
  Dioph {v : Fin 3 → Nat | IsCipherOf (v 0) (v 1) id (v 2)}

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexTargets
