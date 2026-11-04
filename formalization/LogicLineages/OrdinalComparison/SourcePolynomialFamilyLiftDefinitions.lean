module
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift
def prefixVariable (Γ : List Ty) : {n : Nat} → Fin n →
    Variable (List.replicate n FunctionalDetector.unary ++ Γ) FunctionalDetector.unary
  | _+1,i => Fin.cases .here (fun j => .there (prefixVariable Γ j)) i
def oldVariable (Γ : List Ty) (τ : Ty) : (n : Nat) → Variable Γ τ →
    Variable (List.replicate n FunctionalDetector.unary ++ Γ) τ
  | 0,x => x
  | n+1,x => .there (oldVariable Γ τ n x)
end LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift
