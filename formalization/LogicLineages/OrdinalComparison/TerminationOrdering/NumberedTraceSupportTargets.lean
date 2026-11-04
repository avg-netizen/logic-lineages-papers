module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedRenamingSupport NumberedPrimaryWeakening

def ActualPackedTraceSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (P : VariablePredicate Gamma)
    (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r → supports P q.2 → supports P r.2

def ActualTypedTraceSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (P : VariablePredicate Gamma)
    (tau : Ty) (count : Nat) (q r : AuxTerm Symbol arity Gamma tau),
    WindowTypedTrace Symbol arity symbols S above Gamma tau count q r → supports P q → supports P r

def ActualTupleTraceSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (P : VariablePredicate Gamma)
    (types : List Ty) (count : Nat) (base target : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma types count base target → supportsArguments P base → supportsArguments P target

def ActualPackedTraceImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (count : Nat) (q : Packed Symbol arity Gamma) (r : Packed Symbol arity Delta),
    WindowTrace Symbol arity symbols S above Delta count (renamePacked rho q) r →
    ∃ source : Packed Symbol arity Gamma, renamePacked rho source = r

def ActualTypedTraceImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (tau : Ty) (count : Nat) (q : AuxTerm Symbol arity Gamma tau) (r : AuxTerm Symbol arity Delta tau),
    WindowTypedTrace Symbol arity symbols S above Delta tau count (NumberedRewriteSyntax.rename q rho) r →
    ∃ source : AuxTerm Symbol arity Gamma tau, NumberedRewriteSyntax.rename source rho = r

def ActualTupleTraceImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (types : List Ty) (count : Nat) (base : AuxArguments Symbol arity Gamma types) (target : AuxArguments Symbol arity Delta types),
    WindowTupleTrace Symbol arity symbols S above Delta types count (renameArguments base rho) target →
    ∃ source : AuxArguments Symbol arity Gamma types, renameArguments source rho = target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSupportTargets
