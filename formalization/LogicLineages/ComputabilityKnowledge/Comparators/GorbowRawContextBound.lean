module

public import LogicLineages.ComputabilityKnowledge.GorbowRawContextBound
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRawContextBound
open GorbowSyntax GorbowFreeSupport
open LogicLineages.ComputabilityKnowledge.GorbowRawContextBound

def TokenBound : Prop := ∀ raw, 0<rawBound raw ∧ ∀ i∈raw,i<rawBound raw

def SupportBound : Prop :=
  (∀ n (t : Term n) i, i∈termSupport t → i<rawBound (GorbowTermPrefixCode.encode t)) ∧
  (∀ n (φ : Formula n) i, i∈formulaSupport φ → i<rawBound (GorbowFormulaPrefixCode.encode φ))

def TypedTransport : Prop :=
  (∀ n (t : Term n), ∃ u : Term (rawBound (GorbowTermPrefixCode.encode t)),
    GorbowContextTransport.term _ t=some u ∧ GorbowTermPrefixCode.encode u=GorbowTermPrefixCode.encode t ∧ termSupport u=termSupport t) ∧
  (∀ n (φ : Formula n), ∃ ψ : Formula (rawBound (GorbowFormulaPrefixCode.encode φ)),
    GorbowContextTransport.formula _ φ=some ψ ∧ GorbowFormulaPrefixCode.encode ψ=GorbowFormulaPrefixCode.encode φ ∧ formulaSupport ψ=formulaSupport φ)

def ParserDomain : Prop :=
  (∀ raw, (∃ t, GorbowTermPrefixCode.decode (rawBound raw) raw=some t) ↔ ∃ (n : Nat) (t : Term n), raw=GorbowTermPrefixCode.encode t) ∧
  (∀ raw, (∃ φ, GorbowFormulaPrefixCode.decode (rawBound raw) raw=some φ) ↔ ∃ (n : Nat) (φ : Formula n), raw=GorbowFormulaPrefixCode.encode φ)

def ExactValidity : Prop :=
  (∀ raw, validAnyTerm raw=true ↔ ∃ (n : Nat) (t : Term n), raw=GorbowTermPrefixCode.encode t) ∧
  (∀ raw, validAnyFormula raw=true ↔ ∃ (n : Nat) (φ : Formula n), raw=GorbowFormulaPrefixCode.encode φ)

def UniformPrograms : Prop := Primrec rawBound ∧ Primrec validAnyTerm ∧ Primrec validAnyFormula

def Target : Prop := TokenBound ∧ SupportBound ∧ TypedTransport ∧ ParserDomain ∧ ExactValidity ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRawContextBound
