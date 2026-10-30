module

public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesDefinitions

@[expose] public section
/-! Literal finite named contexts with first-match shadowing. The typing witness
is lookup, not translation correctness. No alpha-renaming or named substitution
is defined by this parsing interface. -/
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSyntax

abbrev Context := List (Nat × Ty)
def contextTypes (Γ : Context) : List Ty := Γ.map Prod.snd

def lookup : Context → Nat → Option Ty
  | [], _ => none
  | (y, σ) :: Γ, x => if x = y then some σ else lookup Γ x

def variableName : {Γ : Context} → {σ : Ty} → Variable (contextTypes Γ) σ → Nat
  | (x, _) :: _, _, .here => x
  | _ :: _, _, .there v => variableName v

def Visible : {Γ : Context} → {σ : Ty} → Variable (contextTypes Γ) σ → Prop
  | _ :: _, _, .here => True
  | (x, _) :: _, _, .there v => variableName v ≠ x ∧ Visible v

def resolve : (Γ : Context) → (x : Nat) → {σ : Ty} → lookup Γ x = some σ →
    Variable (contextTypes Γ) σ
  | [], _, _, h => nomatch h
  | (y, τ) :: Γ, x, σ, h =>
      if e : x = y then
        have ht : τ = σ := by simpa only [lookup, if_pos e, Option.some.injEq] using h
        ht ▸ Variable.here
      else Variable.there (resolve Γ x (by simpa only [lookup, if_neg e] using h))

inductive NamedTerm (Symbol : Type) (arity : Symbol → Nat) : Context → Ty → Type where
  | var {Γ σ} (x : Nat) (h : lookup Γ x = some σ) : NamedTerm Symbol arity Γ σ
  | app {Γ σ τ} : NamedTerm Symbol arity Γ (.arrow σ τ) →
      NamedTerm Symbol arity Γ σ → NamedTerm Symbol arity Γ τ
  | lam {Γ σ τ} (x : Nat) : NamedTerm Symbol arity ((x, σ) :: Γ) τ →
      NamedTerm Symbol arity Γ (.arrow σ τ)
  | zeroC {Γ} : NamedTerm Symbol arity Γ .ground
  | succC {Γ} : NamedTerm Symbol arity Γ (.arrow .ground .ground)
  | caseC {Γ} (τ : Ty) : NamedTerm Symbol arity Γ τ.caseType
  | recC {Γ} (τ : Ty) : NamedTerm Symbol arity Γ τ.recType
  | ranked {Γ} (s : Symbol) : (Fin (arity s) → NamedTerm Symbol arity Γ .ground) →
      NamedTerm Symbol arity Γ .ground

def erase {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) : Term Symbol arity (contextTypes Γ) τ :=
  match t with
  | .var x h => .var (resolve Γ x h)
  | .app f a => .app (erase f) (erase a)
  | .lam _ body => .lam (erase body)
  | .zeroC => .zeroC
  | .succC => .succC
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .ranked s args => .ranked s (fun i => erase (args i))

def namedSupport {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) : Finset Ty :=
  τ.subtypes.toFinset ∪ match t with
  | .var _ _ | .zeroC | .succC | .caseC _ | .recC _ => ∅
  | .app f a => namedSupport f ∪ namedSupport a
  | .lam _ body => namedSupport body
  | .ranked s args => Finset.univ.biUnion fun i : Fin (arity s) => namedSupport (args i)

def namedDepth {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) : Nat :=
  match t with
  | .var _ _ | .zeroC | .succC | .caseC _ | .recC _ => 0
  | .app f a => max (namedDepth f) (namedDepth a)
  | .lam _ body => namedDepth body + 1
  | .ranked s args => Finset.univ.sup fun i : Fin (arity s) => namedDepth (args i)

def namedOccurrences {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) : List (Nat × Ty) :=
  match t with
  | .var x _ => [(x, τ)]
  | .app f a => namedOccurrences f ++ namedOccurrences a
  | .lam x body => (namedOccurrences body).filter (fun v => v.1 != x)
  | .zeroC | .succC | .caseC _ | .recC _ => []
  | .ranked s args => (List.ofFn fun i : Fin (arity s) => namedOccurrences (args i)).flatten

def namePacked {Γ : Context} (v : SourceFreeOccurrences.PackedVariable (contextTypes Γ)) : Nat × Ty :=
  (variableName v.2, v.1)

end LogicLineages.OrdinalComparison.Source.SourceNamedSyntax
