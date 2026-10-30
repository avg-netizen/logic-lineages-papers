module

public import LogicLineages.OrdinalComparison.SourceTerms

@[expose] public section
/-! Literal paper06 marked/retyped syntax. Arbitrary output retyping and typed
extras are syntactic data, not a claim of comparison or semantic correctness. -/
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedSyntax

inductive Head (Symbol : Type) where
  | zero | succ
  | cases (τ : Ty)
  | recursor (τ : Ty)
  | application (σ τ : Ty)
  | ranked (s : Symbol)

def headArguments {Symbol : Type} (arity : Symbol → Nat) : Head Symbol → List Ty
  | .zero | .succ | .cases _ | .recursor _ => []
  | .application σ τ => [.arrow σ τ, σ]
  | .ranked s => List.replicate (arity s) .ground

def headResult {Symbol : Type} : Head Symbol → Ty
  | .zero => .ground
  | .succ => .arrow .ground .ground
  | .cases τ => τ.caseType
  | .recursor τ => τ.recType
  | .application _ τ => τ
  | .ranked _ => .ground

mutual
inductive MarkedTerm (Symbol : Type) (arity : Symbol → Nat) : List Ty → Ty → Type where
  | var {Γ σ} : Variable Γ σ → MarkedTerm Symbol arity Γ σ
  | lam {Γ σ τ} : MarkedTerm Symbol arity (σ :: Γ) τ → MarkedTerm Symbol arity Γ (.arrow σ τ)
  | ordinary {Γ} (h : Head Symbol) : Arguments Symbol arity Γ (headArguments arity h) →
      MarkedTerm Symbol arity Γ (headResult h)
  | marked {Γ} (h : Head Symbol) (output : Ty) :
      Arguments Symbol arity Γ (headArguments arity h) →
      (extraTypes : List Ty) → Arguments Symbol arity Γ extraTypes → MarkedTerm Symbol arity Γ output
inductive Arguments (Symbol : Type) (arity : Symbol → Nat) : List Ty → List Ty → Type where
  | nil {Γ} : Arguments Symbol arity Γ []
  | cons {Γ σ types} : MarkedTerm Symbol arity Γ σ → Arguments Symbol arity Γ types →
      Arguments Symbol arity Γ (σ :: types)
end

def groundArguments {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} :
    (n : Nat) → (Fin n → MarkedTerm Symbol arity Γ .ground) →
      Arguments Symbol arity Γ (List.replicate n .ground)
  | 0, _ => .nil
  | n + 1, f => .cons (f ⟨0, Nat.zero_lt_succ n⟩) (groundArguments n (fun i => f i.succ))

def embed {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : MarkedTerm Symbol arity Γ τ :=
  match t with
  | .var v => .var v
  | .app f a => .ordinary (.application _ _) (.cons (embed f) (.cons (embed a) .nil))
  | .lam body => .lam (embed body)
  | .zeroC => .ordinary .zero .nil
  | .succC => .ordinary .succ .nil
  | .caseC τ => .ordinary (.cases τ) .nil
  | .recC τ => .ordinary (.recursor τ) .nil
  | .ranked s args => .ordinary (.ranked s) (groundArguments (arity s) (fun i => embed (args i)))

def spineHead {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : Option (Head Symbol) :=
  match q with
  | .var _ => none
  | .lam body => spineHead body
  | .ordinary h _ => some h
  | .marked h _ _ _ _ => some h

def markSpine {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : Option (MarkedTerm Symbol arity Γ τ) :=
  match q with
  | .var _ => none
  | .lam body => (markSpine body).map .lam
  | .ordinary h args => some (.marked h (headResult h) args [] .nil)
  | .marked h output args extraTypes extras => some (.marked h output args extraTypes extras)

def originalSpineHead {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : Option (Head Symbol) :=
  match t with
  | .var _ => none
  | .lam body => originalSpineHead body
  | @Term.app _ _ _ σ τ _ _ => some (.application σ τ)
  | .zeroC => some .zero
  | .succC => some .succ
  | .caseC τ => some (.cases τ)
  | .recC τ => some (.recursor τ)
  | .ranked s _ => some (.ranked s)

end LogicLineages.OrdinalComparison.Source.SourceMarkedSyntax
