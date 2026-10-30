module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCode

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalPrefixCode

open PositiveExpression WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCode

def ParsingSound : Prop :=
  ∀ (d k : Nat) (raw rest : List Nat) (t : Term (Fin d)),
    parse d k raw = some (t, rest) → raw = encode t ++ rest

def ParsingComplete : Prop :=
  ∀ (d : Nat) (t : Term (Fin d)) (k : Nat), height t ≤ k →
    ∀ rest : List Nat, parse d k (encode t ++ rest) = some (t, rest)

def FiniteFuel : Prop :=
  ∀ (d : Nat) (t : Term (Fin d)), height t ≤ (encode t).length + 1

def DecoderExact : Prop :=
  ∀ (d : Nat) (raw : List Nat) (t : Term (Fin d)), decode d raw = some t ↔ raw = encode t

def EncodingInjective : Prop :=
  ∀ d : Nat, Function.Injective (@encode d)

def EmbedCompatibility : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)), encode (embed e) = CircuitReduction.encodeExpr (e.rename Fin.val)

def Target : Prop := ParsingSound ∧ ParsingComplete ∧ FiniteFuel ∧ DecoderExact ∧ EncodingInjective ∧ EmbedCompatibility

end LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalPrefixCode
