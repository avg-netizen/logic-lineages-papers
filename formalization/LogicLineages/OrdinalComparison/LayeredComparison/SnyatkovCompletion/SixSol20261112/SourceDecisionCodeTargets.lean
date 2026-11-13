module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionTargets
open SourceDecision NonlinearProjectionCompletion CommonLayerSyntax

def LiteralTermEmbedding : Prop := ∀ t : BaseTerm,
  embedTerm t.encode = (OriginalSourceElimination.embed t).encode
def LiteralBinderCompiler : Prop := ∀ (i : Nat) (p : Matrix),
  binder i p.encode = (OriginalSourceElimination.eliminateBinder i p).encode
def LiteralSourceCompiler : Prop := ∀ p : SourceFormula,
  eliminate p.encode = (OriginalSourceElimination.eliminate p).encode
def ActualCompilerPrograms : Prop := Computable embedTerm ∧ Computable₂ binder ∧ Computable eliminate

def GroundTermCalibration : Prop := ∀ t : Term, groundTerm t.encode = t.value (fun _ => 0)
def GroundMatrixCalibration : Prop := ∀ p : Matrix,
  groundMatrix p.encode = true ↔ p.eval (fun _ => 0)
def ActualEvaluationPrograms : Prop := Computable groundTerm ∧ Computable groundMatrix ∧ Computable answer

/-- Full original source semantics, all Boolean/binder patterns and nonlinear
terms. This explicitly includes effectivity and original free-name support. -/
def EffectiveOriginalSourceElimination : Prop :=
  ∃ program : Nat → Nat, Computable program ∧
    (∀ p : SourceFormula, program p.encode = (OriginalSourceElimination.eliminate p).encode) ∧
    (∀ (p : SourceFormula) (ν : Nat → Nat),
      (OriginalSourceElimination.eliminate p).eval ν ↔ p.eval ν) ∧
    (∀ (p : SourceFormula) (i : Nat),
      i ∈ (OriginalSourceElimination.eliminate p).variables → i ∈ p.variables)

/-- The numbered source08 supplier on its literal complete sentence coding.
There is no source-shape test, supplied oracle, or unproved semantic premise. -/
def FullSourceDecision : Prop :=
  ∃ decision : Nat → Bool, Computable decision ∧
    ∀ (p : SourceFormula), p.variables = [] → ∀ ν : Nat → Nat,
      decision p.encode = true ↔ p.eval ν

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionTargets
