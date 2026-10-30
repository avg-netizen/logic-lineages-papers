module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaComposition
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaSubstitution
open LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition

def LiftComposition : Prop := ∀ l m n (σ : Fin l → Term m) (τ : Fin m → Term n),
  (fun i => GorbowSubstitution.substitute (liftSubstitute τ) (liftSubstitute σ i))=
    liftSubstitute (fun i => GorbowSubstitution.substitute τ (σ i))

def Composition : Prop := ∀ l m n (φ : Formula l) (σ : Fin l → Term m) (τ : Fin m → Term n),
  substituteFormula τ (substituteFormula σ φ)=
    substituteFormula (fun i => GorbowSubstitution.substitute τ (σ i)) φ

def OccurrenceLocality : Prop := ∀ n m (φ : Formula n) (σ τ : Fin n → Term m),
  (∀ i, i.val∈formulaSupport φ → σ i=τ i) → substituteFormula σ φ=substituteFormula τ φ

def NamedSyntax : Prop := ∀ n (v : Fin n) (φ : Formula n) (t : Term 0),
  namedClosedInstance v φ t=GorbowStandardInstances.instantiate (selectVariable v φ) t

def NamedSemantics : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∀ (t : Term 0) I ρ, (namedClosedInstance v φ t).realize I Fin.elim0 ↔
    φ.realize I (assignAt ρ v (t.realize I Fin.elim0))

def ContextInvariance : Prop := ∀ n m (v : Fin n) (w : Fin m), v.val=w.val →
  ∀ (φ : Formula n) (ψ : Formula m), GorbowContextTransport.formula m φ=some ψ →
  ∀ t : Term 0, namedClosedInstance v φ t=namedClosedInstance w ψ t

def Target : Prop := LiftComposition ∧ Composition ∧ OccurrenceLocality ∧ NamedSyntax ∧ NamedSemantics ∧ ContextInvariance
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaComposition
