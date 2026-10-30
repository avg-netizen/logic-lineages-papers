module
public import LogicLineages.OrdinalComparison.SourceTerms
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
public import Mathlib.Data.List.OfFn

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

abbrev OrdinalComponent (Γ : List Ty) :=
  Σ σ : Ty, Variable Γ σ × Fin (σ.level + 1)

abbrev OrdinalExpression (Γ : List Ty) :=
  LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term (OrdinalComponent Γ)

/-- Every component of the actual typed variable vector, without collapsing
higher-type variables to ground names. -/
def ordinalVariableVector {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) :
    List (OrdinalExpression Γ) :=
  List.ofFn fun i : Fin (σ.level + 1) => .var ⟨σ, v, i⟩

def ordinalComponentRename {Γ Δ : List Ty} (ρ : Renaming Γ Δ) :
    OrdinalComponent Γ → OrdinalComponent Δ
  | ⟨σ, v, i⟩ => ⟨σ, ρ v, i⟩

def ordinalExpressionRename {Γ Δ : List Ty} (ρ : Renaming Γ Δ) :
    OrdinalExpression Γ → OrdinalExpression Δ :=
  LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.substitute
    (fun c => .var (ordinalComponentRename ρ c))

/-- Literal X:=1 for the newly bound head vector; old variables retain their
original context positions. This is not general source-term substitution. -/
def ordinalHeadClosureComponent {Γ : List Ty} {σ : Ty} :
    OrdinalComponent (σ :: Γ) → OrdinalExpression Γ
  | ⟨_, .here, _⟩ => .one
  | ⟨τ, .there v, i⟩ => .var ⟨τ, v, i⟩

def ordinalHeadClosure {Γ : List Ty} {σ : Ty} :
    OrdinalExpression (σ :: Γ) → OrdinalExpression Γ :=
  LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.substitute
    ordinalHeadClosureComponent

end LogicLineages.OrdinalComparison.Source
