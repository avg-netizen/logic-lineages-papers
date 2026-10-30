module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaPrefixCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode

def ParsingSound : Prop :=
  ∀ (n k : Nat) (raw rest : List Nat) (φ : Formula n),
    parse n k raw = some (φ, rest) → raw = encode φ ++ rest

def ParsingComplete : Prop :=
  ∀ (n : Nat) (φ : Formula n) (k : Nat), height φ ≤ k →
    ∀ rest : List Nat, parse n k (encode φ ++ rest) = some (φ, rest)

def FiniteFuel : Prop :=
  ∀ (n : Nat) (φ : Formula n), height φ ≤ (encode φ).length + 1

def DecoderExact : Prop :=
  ∀ (n : Nat) (raw : List Nat) (φ : Formula n), decode n raw = some φ ↔ raw = encode φ

def EncodingInjective : Prop :=
  ∀ n : Nat, Function.Injective (@encode n)

def BinderContext : Prop :=
  ∀ (n k : Nat) (raw rest : List Nat) (φ : Formula (n + 1)),
    parse (n + 1) k raw = some (φ, rest) →
      parse n (k + 1) (10 :: raw) = some (.all φ, rest) ∧
      parse n (k + 1) (11 :: raw) = some (.ex φ, rest)

def Target : Prop := ParsingSound ∧ ParsingComplete ∧ FiniteFuel ∧ DecoderExact ∧
  EncodingInjective ∧ BinderContext
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaPrefixCode
