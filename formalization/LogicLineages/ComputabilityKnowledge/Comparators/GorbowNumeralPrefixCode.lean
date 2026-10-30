module

public import LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumeralPrefixCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCode

def PrefixExact : Prop := ∀ raw n rest,
  parse raw=some (n,rest) ↔ raw=GorbowCodeConstructors.numeral n ++ rest

def ClosedExact : Prop := ∀ raw n,
  decode raw=some n ↔ raw=GorbowCodeConstructors.numeral n

def TypedCalibration : Prop := ∀ k n rest,
  parse (GorbowTermPrefixCode.encode (Term.numeral (n:=k) n) ++ rest)=some (n,rest) ∧
  decode (GorbowTermPrefixCode.encode (Term.numeral (n:=k) n))=some n

def Rejection : Prop :=
  (∀ raw, parse raw=none ↔ ¬ ∃ n rest, raw=GorbowCodeConstructors.numeral n ++ rest) ∧
  (∀ raw, decode raw=none ↔ ¬ ∃ n, raw=GorbowCodeConstructors.numeral n)

def UniformPrograms : Prop := Primrec leadingSucc ∧ Primrec parse ∧ Primrec decode

def Target : Prop := PrefixExact ∧ ClosedExact ∧ TypedCalibration ∧ Rejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumeralPrefixCode
