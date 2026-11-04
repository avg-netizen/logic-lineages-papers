module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimarySubstitution

def ActualPackedTraceSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r →
    ∃ m : Nat, m ≤ count ∧ WindowTrace Symbol arity symbols S above Delta m (substitutePacked theta q) (substitutePacked theta r)

def ActualTypedTraceSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (tau : Ty) (count : Nat) (q r : AuxTerm Symbol arity Gamma tau),
    WindowTypedTrace Symbol arity symbols S above Gamma tau count q r →
    ∃ m : Nat, m ≤ count ∧ WindowTypedTrace Symbol arity symbols S above Delta tau m (substitute q theta) (substitute r theta)

def ActualTupleTraceSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (types : List Ty) (count : Nat) (base target : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma types count base target →
    ∃ m : Nat, m ≤ count ∧ WindowTupleTrace Symbol arity symbols S above Delta types m
      (substituteArguments base theta) (substituteArguments target theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionTargets
