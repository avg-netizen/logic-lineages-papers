module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinearDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.Targets
open FirstOrder Language

def TermTranslationExact : Prop :=
  ∀ n (t : Language.presburger.Term (Fin n)) (v : Fin n → Nat),
    (Affine.ofTerm t).eval (fun i => (v i : Int)) = ((t.realize v : Nat) : Int)

def LastVariableSplitExact : Prop :=
  ∀ n (t : Affine (n + 1)) (v : Fin n → Int) x,
    t.eval (Fin.snoc v x) = (Affine.dropLast t).eval v + Affine.lastCoeff t * x

def SubstitutionExact : Prop :=
  ∀ n (t : Affine (n + 1)) (s : Affine n) (v : Fin n → Int),
    (Affine.substLast t s).eval v = t.eval (Fin.snoc v (s.eval v))

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear.Targets
