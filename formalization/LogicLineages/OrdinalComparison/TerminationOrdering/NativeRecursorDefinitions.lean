module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursor
open Source Source.SourceMarkedSyntax RecursiveComparison LiteralContexts

abbrev stepType (τ : Ty) : Ty := .arrow .ground (.arrow τ τ)

def recursorTerm {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) : Term Symbol arity Γ τ := .app (.app (.app (.recC τ) n) A) B

def successorContractum {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) : Term Symbol arity Γ τ := .app (.app A n) (recursorTerm n A B)

def P {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) (ρ : Ty) : MarkedTerm Symbol arity Γ ρ :=
  .marked (.application τ τ) ρ
    (.cons (embed (.app (.app (.recC τ) (.app .succC n)) A)) (.cons (embed B) .nil)) [] .nil

def C2 {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) (ρ : Ty) : MarkedTerm Symbol arity Γ ρ :=
  .marked (.application (stepType τ) (.arrow τ τ)) ρ
    (.cons (embed (.app (.recC τ) (.app .succC n))) (.cons (embed A) .nil)) [τ] (.cons (P n A B τ) .nil)

def C1 {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) (ρ : Ty) : MarkedTerm Symbol arity Γ ρ :=
  .marked (.application .ground (.arrow (stepType τ) (.arrow τ τ))) ρ
    (.cons (embed (.recC τ)) (.cons (embed (.app .succC n)) .nil)) [stepType τ,τ]
    (.cons (C2 n A B (stepType τ)) (.cons (C2 n A B τ) .nil))

def C0 {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ))
    (B : Term Symbol arity Γ τ) (ρ : Ty) : MarkedTerm Symbol arity Γ ρ :=
  .marked (.recursor τ) ρ .nil [.ground,stepType τ,τ]
    (.cons (C1 n A B .ground) (.cons (C1 n A B (stepType τ)) (.cons (C1 n A B τ) .nil)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursor
