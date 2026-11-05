module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseTargets
open FiniteCoefficientBase Source Source.ForwardTranslation CommonLayerSyntax
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ActualCoefficient : Prop := ∀ c k, coefficient c = some k →
  0 < k ∧ c.evaluate.1.repr = (k : Ordinal)

def ExactExpansion : Prop := ∀ k t,
  (∀ ν, (expand k t).value ν = actualCollapse (Ordinal.omega0 * (k : Ordinal) + (t.value ν : Ordinal))) ∧
  (expand k t).variables = t.variables

def ActualScalar : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) t,
  compile index s = some t →
  (∀ ν, t.value ν = s.value (fun i => ν (index i))) ∧ t.variables = support index s

/-- A successful ORIGINAL scalar extraction from a literal no-Omega assignment
always passes. The source-domain condition is syntactic, not an assumed compiler
success or assumed semantically finite ordinal evaluator. -/
def NoOmegaSource : Prop := ∀ (Γ : List Ty) (e : OrdinalExpression Γ) s,
  compileScalar e = some s → SourceClasses.noOmega e = true →
  ∀ index : OrdinalComponent Γ → Nat, ∃ t, compile index s = some t

/-- Literal canonical default-policy assignment of every original recursor-free
source with ground free context, with NO bound on internal types or binders.
The code/semantic result concerns its actual scalar coordinate; vector decisions
and the whole finite-coefficient source theorem remain separate. -/
def ActualRecursorFreeSource : Prop := ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ τ (e : OriginalTerm Γ τ), SourceClasses.recursorFree e = true →
  ∃ (v : OrdinalVector Γ τ.level) (s : Scalar (OrdinalComponent Γ)) (t : BaseTerm),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy e = some v ∧
    compileScalar (v 0) = some s ∧ compile rawIndex s = some t ∧
    ∀ ν : Nat → Nat, (t.value ν : Ordinal) = denote (fun c => (ν (rawIndex c) : Ordinal)) (v 0)

def LiteralNumericCalibration : Prop :=
  (∀ c, Code.coefficient (closedPositiveCode c) = coefficient c) ∧
  (∀ k t, Code.expand k t.encode = (expand k t).encode) ∧
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
    Code.compile (scalarSyntaxCode index s) = (compile index s).map BaseTerm.encode

def ActualNumericPrograms : Prop :=
  Computable Code.coefficient ∧ Primrec₂ Code.expand ∧ Computable Code.compile

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseTargets
