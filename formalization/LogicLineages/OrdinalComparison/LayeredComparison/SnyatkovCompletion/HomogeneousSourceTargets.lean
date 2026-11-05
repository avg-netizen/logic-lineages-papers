module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceTargets
open HomogeneousSource

def LiteralReconstruction : Prop := ∀ p : SourceFormula,
  SourceParameterDecision.existsBind (peelExists p).1 (peelExists p).2 = p ∧
    SourceParameterDecision.forallBind (peelForall p).1 (peelForall p).2 = p

def ExactDecisionDomain : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (decide values p).isSome = admissible p

def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula), admissible p = true → ∀ b : Bool,
  decide values p = some b ↔ (p.eval (PlainParameterDecision.valuation values) ↔ b = true)

def LiteralCodeData : Prop := ∀ p : SourceFormula,
  Code.peelExists p.encode = ((peelExists p).1, (peelExists p).2.encode) ∧
  Code.peelForall p.encode = ((peelForall p).1, (peelForall p).2.encode) ∧
  Code.admissible p.encode = admissible p ∧
  ∀ values : List Nat, Code.decide values p.encode = decide values p

def ActualNumericPrograms : Prop :=
  Primrec Code.peelExists ∧ Primrec Code.peelForall ∧ Primrec Code.admissible ∧ Primrec₂ Code.decide

def ActualRawDecision : Prop := ∀ (values : List Nat) (code : Nat),
  (Code.decide values code).isSome = admissible (SourceFormulaCodec.decode code) ∧
  (admissible (SourceFormulaCodec.decode code) = true → ∀ b : Bool,
    Code.decide values code = some b ↔
      ((SourceFormulaCodec.decode code).eval (PlainParameterDecision.valuation values) ↔ b = true))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceTargets
