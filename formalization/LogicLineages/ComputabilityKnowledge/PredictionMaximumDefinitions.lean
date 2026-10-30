module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListDefinitions
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
/-! Actual ordinary-program maxima for paper14 eq:bounds and lem:list.
The list selection may be noncomputable; evaluating its compiled finite
maximum uses only ordinary input codes. Empty lists extend the bound by 0. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionMaximum
open PredictionLearning PredictionCanonicalList

def prefixRun (c : Code) : Nat → Part Nat
  | 0 => Nat.Partrec.Code.eval c 0
  | n + 1 => (prefixRun c n).bind fun v =>
      (Nat.Partrec.Code.eval c (n + 1)).bind fun w => Part.some (max v w)

def familySteps (codes : List Code) (n : Nat) : Nat → Part Nat
  | 0 => Part.some 0
  | k + 1 => (familySteps codes n k).bind fun v =>
      (prefixRun (codes.getD k Nat.Partrec.Code.zero) n).bind fun w => Part.some (max v w)

def familyRun (codes : List Code) (n : Nat) : Part Nat := familySteps codes n codes.length

noncomputable def evalValue (c : Code) (n : Nat) : Nat := by
  classical exact if h : (Nat.Partrec.Code.eval c n).Dom then (Nat.Partrec.Code.eval c n).get h else 0

noncomputable def maximumValue (codes : List Code) (n : Nat) : Nat :=
  (Finset.range codes.length).sup fun i =>
    (Finset.range (n + 1)).sup fun j => evalValue (codes.getD i Nat.Partrec.Code.zero) j

def compileMaximum (universal : Code) (codes : List Code) : Code :=
  Nat.Partrec.Code.curry universal (Encodable.encode codes)

def CompilerSemantics (universal : Code) : Prop :=
  ∀ codes : List Code, ∀ n : Nat,
    Nat.Partrec.Code.eval (compileMaximum universal codes) n = familyRun codes n

noncomputable def canonicalPrefix (m : Nat) : List Code := (List.range m).map canonicalCode
noncomputable def canonicalBound (m n : Nat) : Nat :=
  (Finset.range m).sup fun i => (Finset.range (n + 1)).sup fun j => evalValue (canonicalCode i) j

end LogicLineages.ComputabilityKnowledge.PredictionMaximum
