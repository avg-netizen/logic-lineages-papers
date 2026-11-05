module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsTargets
open CommonLayerSyntax SourceRows

def ExactLocalAtomIntroduction : Prop := ∀ (strict : Bool) (a b : BaseTerm) (ν : Nat → Nat),
  (localAtom strict a b).eval ν ↔
    if strict then a.value ν < b.value ν else a.value ν = b.value ν

def ExactSourceIntroduction : Prop := ∀ (p : SourceFormula) (ν : Nat → Nat),
  (SourceRows.translate p).eval ν ↔ p.eval ν

def ExactFreeVariableMembership : Prop := ∀ (p : SourceFormula) (i : Nat),
  i ∈ (SourceRows.translate p).variables ↔ i ∈ p.variables

def LiteralSourceCompilerCalibration : Prop := ∀ p : SourceFormula,
  SourceRows.Code.translate p.encode = (SourceRows.translate p).encode

def ActualSourceNumericProgram : Prop := Primrec SourceRows.Code.translate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsTargets
