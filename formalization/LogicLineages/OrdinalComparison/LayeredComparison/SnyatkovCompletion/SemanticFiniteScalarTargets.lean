module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarTargets
open SemanticFiniteScalar Source.ForwardTranslation CommonLayerSyntax

def ExactSuccessClass : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
  (∃ t, compile index s = some t) ↔ finiteHeads s

def ActualScalar : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) t,
  compile index s = some t →
  (∀ ν, t.value ν = s.value (fun i => ν (index i))) ∧
    t.variables = FiniteCoefficientBase.support index s

def LiteralNumericCalibration : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
  Code.compile (scalarSyntaxCode index s) = (compile index s).map BaseTerm.encode

/-- Every accepted structural translation is preserved as the identical BASE
syntax, not merely an extensionally equal value. No old compiler is edited. -/
def StructuralExtension : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) t,
  FiniteCoefficientBase.compile index s = some t → compile index s = some t

def ActualNumericProgram : Prop := Computable Code.compile
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarTargets
