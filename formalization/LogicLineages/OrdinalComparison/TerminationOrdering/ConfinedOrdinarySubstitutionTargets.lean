module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport Source.SourceFreeOccurrences RecursiveComparison
open LiteralContexts ConfinedOrdinarySubstitution

def ActualSupportPreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (tau : Ty) (s t : Term Symbol arity Gamma tau)
    (theta : Substitution Symbol arity Gamma Delta),
  typeSupport t ⊆ typeSupport s →
  (∀ v∈freeOccurrences t,v∈freeOccurrences s) →
  typeSupport (t.substitute theta) ⊆ typeSupport (s.substitute theta)

def ConfinedSubstitutionStability : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (tau : Ty)
    (s t : Term Symbol arity Gamma tau) (theta : Substitution Symbol arity Gamma Delta),
  (ConfinedWeak above s t → ConfinedWeak above (s.substitute theta) (t.substitute theta)) ∧
  (ConfinedStrict above s t → ConfinedStrict above (s.substitute theta) (t.substitute theta))

def EffectiveConfinedDeciders : Type 1 := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Gamma : List Ty) (tau : Ty)
    (s t : Term Symbol arity Gamma tau), Decidable (ConfinedWeak above s t) × Decidable (ConfinedStrict above s t)

def ConfinedWeakReflexivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (tau : Ty) (s : Term Symbol arity Gamma tau),
  ConfinedWeak above s s

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionTargets
