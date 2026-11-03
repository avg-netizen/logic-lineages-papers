module
public import LogicLineages.OrdinalComparison.SourceMarkedBindingDefinitions

@[expose] public section
/-! Literal typed syntax for source06's numbered auxiliary reduction universe.
Ordinary heads carry the implicit label omega. Numbered heads carry a finite
Nat label, retain the ORIGINAL head's typed base and typed extras, and have an
explicit retyped output. Auxiliary application is DISTINCT from the original
functional application head. No reduction, accessibility or ID1 fact is assumed.

Source: paper06 section "An individual Bachmann--Howard upper bound", and
Kop2012 section5.3. These are syntax/binding suppliers only; the actual numbered
rewrite rules and original-angle simulation are separate pending obligations.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntax
open Source Source.SourceMarkedSyntax

mutual
inductive AuxTerm (Symbol : Type) (arity : Symbol → Nat) : List Ty → Ty → Type where
  | var {Gamma sigma} : Variable Gamma sigma → AuxTerm Symbol arity Gamma sigma
  | lam {Gamma sigma tau} : AuxTerm Symbol arity (sigma::Gamma) tau → AuxTerm Symbol arity Gamma (.arrow sigma tau)
  | app {Gamma sigma tau} : AuxTerm Symbol arity Gamma (.arrow sigma tau) →
      AuxTerm Symbol arity Gamma sigma → AuxTerm Symbol arity Gamma tau
  | bottom {Gamma} (tau : Ty) : AuxTerm Symbol arity Gamma tau
  | ordinary {Gamma} (f : Head Symbol) : AuxArguments Symbol arity Gamma (headArguments arity f) →
      AuxTerm Symbol arity Gamma (headResult f)
  | numbered {Gamma} (k : Nat) (f : Head Symbol) (tau : Ty) :
      AuxArguments Symbol arity Gamma (headArguments arity f) → (extraTypes : List Ty) →
      AuxArguments Symbol arity Gamma extraTypes → AuxTerm Symbol arity Gamma tau
inductive AuxArguments (Symbol : Type) (arity : Symbol → Nat) : List Ty → List Ty → Type where
  | nil {Gamma} : AuxArguments Symbol arity Gamma []
  | cons {Gamma sigma types} : AuxTerm Symbol arity Gamma sigma → AuxArguments Symbol arity Gamma types →
      AuxArguments Symbol arity Gamma (sigma::types)
end

mutual
def rename {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (rho : Renaming Gamma Delta) : AuxTerm Symbol arity Delta tau :=
  match q with
  | .var v => .var (rho v)
  | .lam body => .lam (rename body rho.lift)
  | .app f a => .app (rename f rho) (rename a rho)
  | .bottom tau => .bottom tau
  | .ordinary f base => .ordinary f (renameArguments base rho)
  | .numbered k f tau base types extras => .numbered k f tau (renameArguments base rho) types (renameArguments extras rho)
def renameArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) (rho : Renaming Gamma Delta) : AuxArguments Symbol arity Delta types :=
  match args with
  | .nil => .nil
  | .cons q rest => .cons (rename q rho) (renameArguments rest rho)
end

abbrev Substitution (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty) :=
  ∀ {tau : Ty},Variable Gamma tau → AuxTerm Symbol arity Delta tau

def liftSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma : Ty}
    (rho : Substitution Symbol arity Gamma Delta) : Substitution Symbol arity (sigma::Gamma) (sigma::Delta)
  | _,.here => .var .here
  | _,.there v => rename (rho v) (Renaming.weaken Delta sigma)

def singleSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma : Ty}
    (a : AuxTerm Symbol arity Gamma sigma) : Substitution Symbol arity (sigma::Gamma) Gamma
  | _,.here => a
  | _,.there v => .var v

mutual
def substitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (rho : Substitution Symbol arity Gamma Delta) : AuxTerm Symbol arity Delta tau :=
  match q with
  | .var v => rho v
  | .lam body => .lam (substitute body (liftSubstitution rho))
  | .app f a => .app (substitute f rho) (substitute a rho)
  | .bottom tau => .bottom tau
  | .ordinary f base => .ordinary f (substituteArguments base rho)
  | .numbered k f tau base types extras => .numbered k f tau (substituteArguments base rho) types (substituteArguments extras rho)
def substituteArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) (rho : Substitution Symbol arity Gamma Delta) : AuxArguments Symbol arity Delta types :=
  match args with
  | .nil => .nil
  | .cons q rest => .cons (substitute q rho) (substituteArguments rest rho)
end

def appendArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys) :
    AuxArguments Symbol arity Gamma (xs++ys) :=
  match a with
  | .nil => b
  | .cons q rest => .cons q (appendArguments rest b)

mutual
def canonical {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (n : Nat) (q : MarkedTerm Symbol arity Gamma tau) : AuxTerm Symbol arity Gamma tau :=
  match q with
  | .var v => .var v
  | .lam body => .lam (canonical n body)
  | .ordinary f base => .ordinary f (canonicalArguments n base)
  | .marked f tau base types extras => .numbered n f tau (canonicalArguments n base) types (canonicalArguments n extras)
def canonicalArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma types) : AuxArguments Symbol arity Gamma types :=
  match args with
  | .nil => .nil
  | .cons q rest => .cons (canonical n q) (canonicalArguments n rest)
end

/-- The literal ordinary source translation is independent of the proof budget.
Original application is the source functional @ head, not auxiliary app. -/
def translateOriginal {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (s : Term Symbol arity Gamma tau) : AuxTerm Symbol arity Gamma tau := canonical 0 (embed s)

mutual
inductive Represents (Symbol : Type) (arity : Symbol → Nat) (n : Nat) :
    (Gamma : List Ty) → (tau : Ty) → MarkedTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | var {Gamma sigma} (v : Variable Gamma sigma) : Represents Symbol arity n Gamma sigma (.var v) (.var v)
  | lam {Gamma sigma tau} (q : MarkedTerm Symbol arity (sigma::Gamma) tau) (Q : AuxTerm Symbol arity (sigma::Gamma) tau) :
      Represents Symbol arity n (sigma::Gamma) tau q Q → Represents Symbol arity n Gamma (.arrow sigma tau) (.lam q) (.lam Q)
  | ordinary {Gamma} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (values : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      ArgumentsRepresent Symbol arity n Gamma (headArguments arity f) base values →
      Represents Symbol arity n Gamma (headResult f) (.ordinary f base) (.ordinary f values)
  | numbered {Gamma} (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (values : AuxArguments Symbol arity Gamma (headArguments arity f)) (types : List Ty)
      (extras : Arguments Symbol arity Gamma types) (extraValues : AuxArguments Symbol arity Gamma types) (k : Nat) :
      n≤k → ArgumentsRepresent Symbol arity n Gamma (headArguments arity f) base values →
      ArgumentsRepresent Symbol arity n Gamma types extras extraValues →
      Represents Symbol arity n Gamma tau (.marked f tau base types extras) (.numbered k f tau values types extraValues)
inductive ArgumentsRepresent (Symbol : Type) (arity : Symbol → Nat) (n : Nat) :
    (Gamma : List Ty) → (types : List Ty) → Arguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | nil {Gamma} : ArgumentsRepresent Symbol arity n Gamma [] .nil .nil
  | cons {Gamma sigma types} (q : MarkedTerm Symbol arity Gamma sigma) (Q : AuxTerm Symbol arity Gamma sigma)
      (rest : Arguments Symbol arity Gamma types) (values : AuxArguments Symbol arity Gamma types) :
      Represents Symbol arity n Gamma sigma q Q → ArgumentsRepresent Symbol arity n Gamma types rest values →
      ArgumentsRepresent Symbol arity n Gamma (sigma::types) (.cons q rest) (.cons Q values)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntax
