module

public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCode

@[expose] public section

/-! Faithful full-language term syntax, before any arithmetization or DCB.
Computability of code programs is a separate obligation. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermPrefixCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCode

def ParsingSound : Prop :=
  ∀ (n k : Nat) (raw rest : List Nat) (t : Term n),
    parse n k raw = some (t, rest) → raw = encode t ++ rest

def ParsingComplete : Prop :=
  ∀ (n : Nat) (t : Term n) (k : Nat), height t ≤ k →
    ∀ rest : List Nat, parse n k (encode t ++ rest) = some (t, rest)

def FiniteFuel : Prop :=
  ∀ (n : Nat) (t : Term n), height t ≤ (encode t).length + 1

def DecoderExact : Prop :=
  ∀ (n : Nat) (raw : List Nat) (t : Term n), decode n raw = some t ↔ raw = encode t

def EncodingInjective : Prop :=
  ∀ n : Nat, Function.Injective (@encode n)

def VariableDomain : Prop :=
  ∀ (n i k : Nat) (rest : List Nat), n ≤ i → parse n (k + 1) (0 :: i :: rest) = none

def Target : Prop := ParsingSound ∧ ParsingComplete ∧ FiniteFuel ∧ DecoderExact ∧
  EncodingInjective ∧ VariableDomain
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermPrefixCode
