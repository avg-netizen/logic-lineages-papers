module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationTargets
open Cipher CipherRelation

def ConstantArithmeticCharacterization : Prop := ∀ n q c a : Nat,
  Const n q c a ↔ n+1<q ∧ (n=0 ∨ c<2^q) ∧ a=c*ones n q

def MultiplicationArithmeticCharacterization : Prop := ∀ n q a b c : Nat,
  Mult n q a b c ↔ MultEquations n q a b c

/-- Separate validity hypotheses, matching the actual source specification. -/
def AdditionSpecification : Prop := ∀ n q a b c (f g h : Nat → Nat),
  IsCipherOf n q f a → IsCipherOf n q g b → IsCipherOf n q h c →
  (Add a b c ↔ ∀ i, i<n → f i=g i+h i)

def MultiplicationSpecification : Prop := ∀ n q a b c (f g h : Nat → Nat),
  IsCipherOf n q f a → IsCipherOf n q g b → IsCipherOf n q h c →
  (Mult n q a b c ↔ ∀ i, i<n → f i=g i*h i)

def CodeDiophantine : Prop :=
  Dioph {v : Fin 3 → Nat | Code (v 0) (v 1) (v 2)}

def ConstDiophantine : Prop :=
  Dioph {v : Fin 4 → Nat | Const (v 0) (v 1) (v 2) (v 3)}

def AddDiophantine : Prop :=
  Dioph {v : Fin 3 → Nat | Add (v 0) (v 1) (v 2)}

def MultDiophantine : Prop :=
  Dioph {v : Fin 5 → Nat | Mult (v 0) (v 1) (v 2) (v 3) (v 4)}

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationTargets
