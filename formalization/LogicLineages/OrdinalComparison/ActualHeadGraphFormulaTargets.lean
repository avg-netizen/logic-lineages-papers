module
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Targets
open ForwardTranslation Arithmetic

def ExactFinitePrefix : Prop := ∀ (a : ClosedPositive) (c δ : Nat) (t y : Expr) (ν : Nat → Nat),
  (finitePrefix a c δ t y).eval ν ↔
    actualOrdinalNorm (shiftedHead a δ) ≤ t.value ν ∧
    t.value ν < threshold a c δ ∧ y.value ν = actualHeadValue (shiftedHead a δ) (t.value ν)

/-- A semantic helper for a ray tree. The final source target below constructs
and discharges this calibration from the actual unary source, rather than
accepting an assumed observation oracle as completion. -/
def ExactTailFromRay : Prop := ∀ (Γ : List Ty) (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c : Nat),
  (∀ (ρ : Variable (.ground::Γ) .ground → Nat) (r : Nat),
    UnitElimination.Eval q ρ r ↔ r = ActualUnaryRay.rayValue a c (ρ .here)) →
  ∀ (δ : Nat) (t y : Expr) (ν : Nat → Nat),
    (tail q a c δ t y).eval ν ↔
      threshold a c δ ≤ t.value ν ∧ y.value ν = actualHeadValue (shiftedHead a δ) (t.value ν)

/-- Complete genuine graph, for every actual unary K and every fixed finite
upward shift. Every source leaf is actual and ground-context only. Shared
input expressions t/y are arbitrary, so no independent copies are introduced.
This target is semantic syntax assembly; a numeric compiler is still separate. -/
def ActualWholeGenuineGraph : Prop := ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround 1).level) (a : ClosedPositive) (c : Nat)
      (q : UnitElimination.Tree (Nat×Nat) (.ground::Γ)),
    ActualUnaryRay.Constants K u a c ∧
    UnitElimination.build ((.ground::Γ).length+1) (ActualUnaryRay.source K) = some q ∧
    (∀ s ∈ UnitElimination.sources (UnitElimination.realize q), ∀ σ ∈ s.1, σ = Ty.ground) ∧
    ∀ (δ : Nat) (t y : Expr) (ν : Nat → Nat),
      (graph (UnitElimination.realize q) a c δ t y).eval ν ↔
        actualOrdinalNorm (shiftedHead a δ) ≤ t.value ν ∧
        y.value ν = actualHeadValue (shiftedHead a δ) (t.value ν)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Targets
