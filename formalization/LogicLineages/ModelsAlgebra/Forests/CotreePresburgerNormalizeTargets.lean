module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.Targets
open CotreePresburgerLinear CotreePresburgerUnit

def CoefficientModulusPositive : Prop := ∀ n (p : QF (n + 1)), 0 < coefficientModulus p

def AdjustmentExact : Prop :=
  ∀ n (p : QF (n + 1)) (v : Fin n → Int) (x : Int),
    evalUnit (adjust (coefficientModulus p) p) v ((coefficientModulus p : Int) * x) =
      evalQF p (Fin.snoc v x)

def NormalizationExact : Prop :=
  ∀ n (p : QF (n + 1)) (v : Fin n → Int),
    (∃ x : Nat, evalQF p (Fin.snoc v (x : Int)) = true) ↔
      ∃ y : Nat, evalUnit (normalize p) v (y : Int) = true

def EliminationExact : Prop :=
  ∀ n (p : QF (n + 1)) (v : Fin n → Int),
    evalQF (eliminate p) v = true ↔ ∃ x : Nat, evalQF p (Fin.snoc v (x : Int)) = true

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalize.Targets
