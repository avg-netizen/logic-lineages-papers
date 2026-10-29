module
public import LogicLineages.OrdinalComparison.SourceTypes

@[expose] public section

/-!
# An intrinsically typed Gödel-T kernel

Native constants keep their literal curried types and applications remain
explicit nodes. An optional disjoint ranked ground signature has genuine
finite-arity nodes; it is not an uncurrying of the native case functional.

Binding is represented by typed de Bruijn variables. Translation between this
kernel and named source syntax is a separate pending correspondence theorem;
no comparison or reduction theorem assumes that translation as a field.
-/

namespace LogicLineages.OrdinalComparison.Source

inductive Variable : List Ty → Ty → Type where
  | here {Γ : List Ty} {σ : Ty} : Variable (σ :: Γ) σ
  | there {Γ : List Ty} {σ τ : Ty} : Variable Γ σ → Variable (τ :: Γ) σ

abbrev Renaming (Γ Δ : List Ty) := ∀ {σ : Ty}, Variable Γ σ → Variable Δ σ

def Renaming.lift {Γ Δ : List Ty} {τ : Ty} (ρ : Renaming Γ Δ) :
    Renaming (τ :: Γ) (τ :: Δ)
  | _, .here => .here
  | _, .there v => .there (ρ v)

def Renaming.weaken (Γ : List Ty) (τ : Ty) : Renaming Γ (τ :: Γ) :=
  fun v => .there v

inductive Term (Symbol : Type) (arity : Symbol → Nat) : List Ty → Ty → Type where
  | var {Γ : List Ty} {σ : Ty} : Variable Γ σ → Term Symbol arity Γ σ
  | app {Γ : List Ty} {σ τ : Ty} :
      Term Symbol arity Γ (.arrow σ τ) → Term Symbol arity Γ σ → Term Symbol arity Γ τ
  | lam {Γ : List Ty} {σ τ : Ty} :
      Term Symbol arity (σ :: Γ) τ → Term Symbol arity Γ (.arrow σ τ)
  | zeroC {Γ : List Ty} : Term Symbol arity Γ .ground
  | succC {Γ : List Ty} : Term Symbol arity Γ (.arrow .ground .ground)
  | caseC {Γ : List Ty} (τ : Ty) : Term Symbol arity Γ τ.caseType
  | recC {Γ : List Ty} (τ : Ty) : Term Symbol arity Γ τ.recType
  | ranked {Γ : List Ty} (s : Symbol) :
      (Fin (arity s) → Term Symbol arity Γ .ground) → Term Symbol arity Γ .ground

def Term.rename {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) {Δ : List Ty} (ρ : Renaming Γ Δ) : Term Symbol arity Δ τ :=
  match t with
  | .var v => .var (ρ v)
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .lam body => .lam (body.rename ρ.lift)
  | .zeroC => .zeroC
  | .succC => .succC
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .ranked s args => .ranked s (fun i => (args i).rename ρ)

abbrev Substitution (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) :=
  ∀ {σ : Ty}, Variable Γ σ → Term Symbol arity Δ σ

def Substitution.lift {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (s : Substitution Symbol arity Γ Δ) : Substitution Symbol arity (τ :: Γ) (τ :: Δ)
  | _, .here => .var .here
  | _, .there v => (s v).rename (Renaming.weaken Δ τ)

def Substitution.single {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (a : Term Symbol arity Γ τ) : Substitution Symbol arity (τ :: Γ) Γ
  | _, .here => a
  | _, .there v => .var v

def Term.substitute {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) {Δ : List Ty} (s : Substitution Symbol arity Γ Δ) :
    Term Symbol arity Δ τ :=
  match t with
  | .var v => s v
  | .app f a => .app (f.substitute s) (a.substitute s)
  | .lam body => .lam (body.substitute s.lift)
  | .zeroC => .zeroC
  | .succC => .succC
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .ranked h args => .ranked h (fun i => (args i).substitute s)

inductive RootReduction (Symbol : Type) (arity : Symbol → Nat) :
    {Γ : List Ty} → {τ : Ty} → Term Symbol arity Γ τ → Term Symbol arity Γ τ → Prop where
  | beta {Γ : List Ty} {σ τ : Ty}
      (body : Term Symbol arity (σ :: Γ) τ) (a : Term Symbol arity Γ σ) :
      RootReduction Symbol arity (.app (.lam body) a) (body.substitute (Substitution.single a))
  | caseZero {Γ : List Ty} {τ : Ty} (a b : Term Symbol arity Γ τ) :
      RootReduction Symbol arity (.app (.app (.app (.caseC τ) .zeroC) a) b) a
  | caseSucc {Γ : List Ty} {τ : Ty} (n : Term Symbol arity Γ .ground)
      (a b : Term Symbol arity Γ τ) :
      RootReduction Symbol arity (.app (.app (.app (.caseC τ) (.app .succC n)) a) b) b
  | recZero {Γ : List Ty} {τ : Ty}
      (step : Term Symbol arity Γ (.arrow .ground (.arrow τ τ))) (seed : Term Symbol arity Γ τ) :
      RootReduction Symbol arity (.app (.app (.app (.recC τ) .zeroC) step) seed) seed
  | recSucc {Γ : List Ty} {τ : Ty} (n : Term Symbol arity Γ .ground)
      (step : Term Symbol arity Γ (.arrow .ground (.arrow τ τ))) (seed : Term Symbol arity Γ τ) :
      RootReduction Symbol arity (.app (.app (.app (.recC τ) (.app .succC n)) step) seed)
        (.app (.app step n) (.app (.app (.app (.recC τ) n) step) seed))

/-- Closure of the literal root rules in all typed one-hole contexts. -/
inductive Reduction (Symbol : Type) (arity : Symbol → Nat) :
    {Γ : List Ty} → {τ : Ty} → Term Symbol arity Γ τ → Term Symbol arity Γ τ → Prop where
  | root {Γ : List Ty} {τ : Ty} {s t : Term Symbol arity Γ τ} :
      RootReduction Symbol arity s t → Reduction Symbol arity s t
  | appFunction {Γ : List Ty} {σ τ : Ty} {f g : Term Symbol arity Γ (.arrow σ τ)}
      (a : Term Symbol arity Γ σ) :
      Reduction Symbol arity f g → Reduction Symbol arity (.app f a) (.app g a)
  | appArgument {Γ : List Ty} {σ τ : Ty} (f : Term Symbol arity Γ (.arrow σ τ))
      {a b : Term Symbol arity Γ σ} :
      Reduction Symbol arity a b → Reduction Symbol arity (.app f a) (.app f b)
  | abstraction {Γ : List Ty} {σ τ : Ty} {a b : Term Symbol arity (σ :: Γ) τ} :
      Reduction Symbol arity a b → Reduction Symbol arity (.lam a) (.lam b)
  | rankedArgument {Γ : List Ty} (h : Symbol)
      (as bs : Fin (arity h) → Term Symbol arity Γ .ground) (i : Fin (arity h)) :
      Reduction Symbol arity (as i) (bs i) →
      (∀ j, j ≠ i → as j = bs j) →
      Reduction Symbol arity (.ranked h as) (.ranked h bs)

end LogicLineages.OrdinalComparison.Source
