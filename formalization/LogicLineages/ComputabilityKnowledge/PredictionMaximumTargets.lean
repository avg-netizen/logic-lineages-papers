module

public import LogicLineages.ComputabilityKnowledge.PredictionMaximumDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionMaximumTargets
open PredictionLearning PredictionCanonicalList PredictionMaximum

def PrefixPartialRecursive : Prop := Partrec₂ prefixRun

def FamilyPartialRecursive : Prop := Partrec₂ familyRun

def TotalMaximumSemantics : Prop :=
  ∀ codes : List Code, (∀ c ∈ codes, TotalNat c) → ∀ n : Nat,
    familyRun codes n = Part.some (maximumValue codes n)

def UniformMaximumCompiler : Prop :=
  ∃ universal : Code, Computable (compileMaximum universal) ∧ CompilerSemantics universal ∧
    ∀ codes : List Code, (∀ c ∈ codes, TotalNat c) →
      TotalNat (compileMaximum universal codes) ∧
      ∀ n : Nat, Nat.Partrec.Code.eval (compileMaximum universal codes) n = Part.some (maximumValue codes n)

def CanonicalOrdinaryBounds : Prop :=
  ∀ universal : Code, CompilerSemantics universal → ∀ m : Nat, 1 ≤ m →
    TotalNat (compileMaximum universal (canonicalPrefix m)) ∧
      ∀ n : Nat, Nat.Partrec.Code.eval (compileMaximum universal (canonicalPrefix m)) n =
        Part.some (canonicalBound m n)

def CanonicalBoundDominance : Prop :=
  (∀ m n i j : Nat, i < m → j ≤ n → evalValue (canonicalCode i) j ≤ canonicalBound m n) ∧
  (∀ n : Nat, Monotone (fun m => canonicalBound m n)) ∧
  (∀ m : Nat, Monotone (canonicalBound m))

end LogicLineages.ComputabilityKnowledge.PredictionMaximumTargets
