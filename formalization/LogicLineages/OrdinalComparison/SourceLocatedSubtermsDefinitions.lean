module
public import LogicLineages.OrdinalComparison.SourceTypeSupportDefinitions
@[expose] public section
/-! Literal original-target subterms and their actual ancestor binder prefix.
The raw ambient context is data; its relation to that prefix is proved, not
stored as a correctness field. -/
namespace LogicLineages.OrdinalComparison.Source.SourceLocatedSubterms

structure LocatedTerm (Symbol : Type) (arity : Symbol → Nat) where
  binders : List Ty
  ambient : List Ty
  resultType : Ty
  body : Term Symbol arity ambient resultType

def children {Symbol : Type} {arity : Symbol → Nat}
    (u : LocatedTerm Symbol arity) : List (LocatedTerm Symbol arity) :=
  match u with
  | ⟨Λ, Ξ, _, t⟩ => match t with
    | .var _ => []
    | .zeroC => []
    | .succC => []
    | .caseC _ => []
    | .recC _ => []
    | .app f a => [⟨Λ, Ξ, _, f⟩, ⟨Λ, Ξ, _, a⟩]
    | @Term.lam _ _ _ σ τ body => [⟨σ :: Λ, σ :: Ξ, τ, body⟩]
    | .ranked s args => List.ofFn fun i : Fin (arity s) => ⟨Λ, Ξ, .ground, args i⟩

def collect {Symbol : Type} {arity : Symbol → Nat} (Λ : List Ty) {Ξ : List Ty} {τ : Ty}
    (t : Term Symbol arity Ξ τ) : List (LocatedTerm Symbol arity) :=
  ⟨Λ, Ξ, τ, t⟩ :: match t with
  | .var _ => []
  | .zeroC => []
  | .succC => []
  | .caseC _ => []
  | .recC _ => []
  | .app f a => collect Λ f ++ collect Λ a
  | @Term.lam _ _ _ σ _ body => collect (σ :: Λ) body
  | .ranked s args => (List.ofFn fun i : Fin (arity s) => collect Λ (args i)).flatten
termination_by structural t

end LogicLineages.OrdinalComparison.Source.SourceLocatedSubterms
