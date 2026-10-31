module
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScopedDAG.Targets
open GroundEquivalence

def Renaming : Prop := ∀ Γ Δ τ (r : Source.Renaming Γ Δ) (d : Input Γ τ),
  (renameInput r d).term=d.term.rename r ∧ (renameInput r d).specs.length=d.specs.length

def Application : Prop := ∀ Γ σ τ (f : Input Γ (.arrow σ τ)) (a : Input Γ σ),
  (application f a).term=.app f.term a.term ∧
  (application f a).specs.length=f.specs.length+a.specs.length+1

def Eraser : Prop := ∀ Γ (a b : Input Γ .ground),
  (eraser a b).term=SourceCollisionCompletion.eraser a.term b.term ∧
  (eraser a b).specs.length=a.specs.length+b.specs.length+2

def Aggregate : Prop := ∀ Γ (es : List (Input Γ .ground × Input Γ .ground)),
  ((aggregate es).1.term,(aggregate es).2.term)=SourceAggregateCompletion.aggregate (equations es) ∧
  (aggregate es).1.specs.length=weight es ∧ (aggregate es).2.specs.length=weight es
end LogicLineages.OrdinalComparison.Source.ScopedDAG.Targets
