module
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.Targets
open SourceCollisionCompletion SourceAggregateCompletion PrimitiveLowering

def ExactRenaming : Prop := ∀ (Γ Δ : List Ty) (τ : Ty) (r : Renaming Γ Δ)
    (t : OriginalTerm Γ τ), Fragment (t.rename r) ↔ Fragment t

def PrimitiveExpressions : Prop := ∀ (Γ : List Ty) (e : Expr Γ), Fragment e.term

def LiteralEraserDetectors : Prop := ∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground),
  Fragment p → Fragment q →
    Fragment (eraser p q) ∧ Fragment (detectorLeft p q) ∧ Fragment (detectorRight p q)

def LiteralAggregate : Prop := ∀ (Γ : List Ty)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
  (∀ e ∈ es,Fragment e.1 ∧ Fragment e.2) →
    Fragment (aggregate es).1 ∧ Fragment (aggregate es).2
end LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.Targets
