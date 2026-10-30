module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalListTargets
open PredictionLearning PredictionCanonicalList

def OrdinaryNumberingCalibration : Prop :=
  (∀ c : Code, codeAt (Encodable.encode c) = c) ∧
    (∀ i : Nat, Encodable.encode (codeAt i) = i)

def UniqueLeastRepresentative : Prop :=
  ∀ c : Code, TotalNat c → ∃! i : Nat, Representative i ∧ SameFunction (codeAt i) c

def InfinitelyManyRepresentatives : Prop := Set.Infinite {i : Nat | Representative i}

def StrictCanonicalEnumeration : Prop :=
  StrictMono canonicalIndex ∧ ∀ n : Nat, Representative (canonicalIndex n)

def ExhaustiveCanonicalCodes : Prop :=
  ∀ c : Code, TotalNat c → ∃! n : Nat, SameFunction (canonicalCode n) c

def ExhaustiveTotalComputableFunctions : Prop :=
  ∀ f : Nat → Nat, Computable f →
    ∃! n : Nat, ∀ x : Nat, Nat.Partrec.Code.eval (canonicalCode n) x = Part.some (f x)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalListTargets
