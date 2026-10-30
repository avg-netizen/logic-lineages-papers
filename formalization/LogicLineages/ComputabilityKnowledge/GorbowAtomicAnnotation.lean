module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCode

@[expose] public section
/-! Decidable annotation domain for literal atomic FS schemas, with original
ambient context and an ordered injective enumeration of exactly the free names.
This does not decide membership in the full source theory or DCB. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotation

def boundedNames (m : Nat) (names : List Nat) : Bool := decide (∀ i ∈ names, i<m)

def uniqueNames (names : List Nat) : Bool :=
  decide (∀ i ∈ List.range names.length, names.idxOf (names.getD i 0)=i)

def coversNames (m : Nat) (raw names : List Nat) : Bool :=
  decide (∀ i ∈ List.range m,
    GorbowSupportCode.occurs 1 m i raw=true ↔ i ∈ names)

def valid (m : Nat) (raw names : List Nat) : Bool :=
  GorbowSyntaxValidation.validFormula m raw && decide (raw.headD 12<3) &&
    boundedNames m names && uniqueNames names && coversNames m raw names
end LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotation
