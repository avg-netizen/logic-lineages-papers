module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPacking
open Elementary Cipher

def indexed {n : Nat} (i : Nat) (ν : Fin n → Nat) : Option (Fin n) → Nat
  | none => i
  | some a => ν a

/-- The six source packing cases, separating the iteration-index parameter
from the remaining original free parameters. -/
def packedConstraint {n k : Nat} (len q I : Nat) (ν : Fin n → Nat) (codes : Fin k → Nat)
    (c : Constraint (Option (Fin n)) (Fin k)) : Prop :=
  match c.rhs with
  | .constant a => CipherRelation.Const len q a (codes c.output)
  | .variable b => codes c.output=codes b
  | .parameter none => codes c.output=I
  | .parameter (some a) => CipherRelation.Const len q (ν a) (codes c.output)
  | .add b d => CipherRelation.Add (codes c.output) (codes b) (codes d)
  | .mul b d => CipherRelation.Mult len q (codes c.output) (codes b) (codes d)

def packedSystem {n k m : Nat} (C : Fin m → Constraint (Option (Fin n)) (Fin k))
    (len q I : Nat) (ν : Fin n → Nat) (codes : Fin k → Nat) : Prop :=
  IsCipherOf len q id I ∧
    (∀ b : Fin k, CipherRelation.Code len q (codes b)) ∧
    ∀ j : Fin m, packedConstraint len q I ν codes (C j)

def packed {n k m : Nat} (C : Fin m → Constraint (Option (Fin n)) (Fin k))
    (len : Nat) (ν : Fin n → Nat) : Prop :=
  ∃ q I : Nat, ∃ codes : Fin k → Nat, packedSystem C len q I ν codes

def pointwise {n k m : Nat} (C : Fin m → Constraint (Option (Fin n)) (Fin k))
    (len : Nat) (ν : Fin n → Nat) : Prop :=
  ∀ i : Nat, i<len → ∃ w : Fin k → Nat, ∀ j : Fin m, (C j).Holds (indexed i ν) w

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPacking
