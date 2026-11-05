module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceTargets
open SourceWitnessTrace

def OriginalEnvironment : Prop := ∀ (ν : Nat → Nat) (p : SourceFormula) (ns : List Nat),
  realizes ν p ns ↔ ns.length = (names p).length ∧ (residual p).eval (updateTrace ν (names p) ns)

def LeastRealizationSound : Prop := ∀ (ν : Nat → Nat) (p : SourceFormula) (ns : List Nat),
  leastRealization ν p ns → realizes ν p ns ∧ p.eval ν

def ActualLeastTrace : Prop := ∀ (values : List Nat) (p : SourceFormula),
  FiniteSearchSource.test p = true → ∀ ns : List Nat,
    solve values p.encode = some ns ↔ leastRealization (PlainParameterDecision.valuation values) p ns

def ExactSourceDomain : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (solve values p.encode).isSome = (FiniteSearchSource.test p && FiniteSearchSource.answer values p) ∧
  (FiniteSearchSource.test p = false → solve values p.encode = none)

def ExactTraceShape : Prop := ∀ (values : List Nat) (p : SourceFormula) (ns : List Nat),
  solve values p.encode = some ns → ns.length = (names p).length

def ActualRawTrace : Prop := ∀ (values : List Nat) (code : Nat),
  FiniteSearchPrograms.Code.test code = true → ∀ ns : List Nat,
    solve values code = some ns ↔ leastRealization (PlainParameterDecision.valuation values) (SourceFormulaCodec.decode code) ns

def ActualComputation : Prop := Computable₂ solve

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceTargets
