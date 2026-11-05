module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelation
open Cipher

def Code (n q a : Nat) : Prop := ∃ f : Nat → Nat, IsCipherOf n q f a

def Const (n q c a : Nat) : Prop :=
  ∃ f : Nat → Nat, IsCipherOf n q f a ∧ ∀ i, i<n → f i=c

/-- Source Code_plus has no validity guard; the three validity hypotheses
belong to its pointwise specification. -/
def Add (a b c : Nat) : Prop := a=b+c

/-- Literal source Code_mult relation, with the same auxiliary variables.
Its empty branch is true for every q,a,b,c, including invalid codes. -/
def Mult (n q a b c : Nat) : Prop :=
  n=0 ∨ (n≠0 ∧ ∃ u u1 r' r'' p : Nat,
    r''=base q ∧ r''=r'+1 ∧
    (n+1<q ∧ u=ones n q ∧ u1=shiftedOnes n q) ∧
    p=(a*u) &&& (r'*u1) ∧ p=(b*c) &&& (r'*u1))

/-- Eliminated arithmetic form of the source multiplication relation. -/
def MultEquations (n q a b c : Nat) : Prop :=
  n=0 ∨ (0<n ∧ n+1<q ∧
    (a*ones n q) &&& ((base q-1)*shiftedOnes n q) =
      (b*c) &&& ((base q-1)*shiftedOnes n q))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelation
