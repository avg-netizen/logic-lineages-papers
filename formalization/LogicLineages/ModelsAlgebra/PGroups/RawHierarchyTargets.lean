module
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def positiveComplexityMonotone : Prop :=
  ∀ (side:Polarity) (α β:Ordinal.{0}), α≠0 → α≤β →
    ∀ (n:ℕ) (φ:Formula n), Complexity side α φ → Complexity side β φ
def rawPiNormalization : Prop :=
  ∀ (α β:Ordinal.{0}), β≠0 → α≤β → ∀ (n:ℕ) (φ:Formula n), Complexity .pi α φ →
    Complexity .pi β (piOneNormalize φ) ∧
      ∀ (G:Type) (R:RawGroupStructure G) (a:Fin n→G),
        (piOneNormalize φ).RawRealize R a ↔ φ.RawRealize R a
def rawWrapperTruth : Prop :=
  ∀ (n:ℕ) (φ:Formula n) (G:Type) (R:RawGroupStructure G) (a:Fin n→G),
    ((piWrap φ).RawRealize R a ↔ φ.RawRealize R a) ∧
    ((sigmaWrap φ).RawRealize R a ↔ φ.RawRealize R a)
def rawDifferencePiLift : Prop :=
  ∀ (α β:Ordinal.{0}), α<β → ∀ (n:ℕ) (d:DifferenceFormula n), d.AtLevel α →
    Complexity .pi β (differencePiLift d) ∧
      ∀ (G:Type) (R:RawGroupStructure G) (a:Fin n→G),
        (differencePiLift d).RawRealize R a ↔ d.RawRealize R a
end LogicLineages.ModelsAlgebra.PGroups.Targets
