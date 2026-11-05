module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsTargets
open NormalForm CommonLayerSyntax SourceBooleanPrograms

def LiteralNameShift : Prop := ∀ (d : Nat) (p : NormalForm.Formula),
  Code.shift d p.encode = (shift d p).encode

def ActualPredicateShift : Prop := ∀ (d s : Nat) (p : SourceFormula),
  shift d (SourceBooleanGraph.predicate s p) = SourceBooleanGraph.predicate (d + s) p

def LiteralPayload : Prop := ∀ p : SourceFormula,
  Code.payload p.encode = (SourceBooleanGraph.test p, (SourceBooleanGraph.forest p).encode,
    (SourceBooleanGraph.predicate 0 p).encode)

def LiteralCompilation : Prop := ∀ p : SourceFormula,
  Code.start p.encode = SourceBooleanGraph.start p ∧
    Code.compile p.encode = (SourceBooleanGraph.compile p).encode

def ActualNumericPrograms : Prop :=
  Primrec₂ Code.shift ∧ Primrec Code.payload ∧ Primrec Code.compile ∧
    Primrec Code.decideExists ∧ Primrec Code.decideForall

def LiteralDecisions : Prop := ∀ p : SourceFormula,
  Code.decideExists p.encode = SourceBooleanGraph.decideExists p ∧
    Code.decideForall p.encode = SourceBooleanGraph.decideForall p

def ActualEncodedDecisions : Prop := ∀ p : SourceFormula, SourceBooleanGraph.test p = true → ∀ b : Bool,
  (Code.decideExists p.encode = some b ↔ ((∃ ν : Nat → Nat, p.eval ν) ↔ b = true)) ∧
    (Code.decideForall p.encode = some b ↔ ((∀ ν : Nat → Nat, p.eval ν) ↔ b = true))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsTargets
