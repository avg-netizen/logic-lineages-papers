module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimaryWeakening

def ActualPackedTraceWeakeningReflection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty) (sigma : Ty) (count : Nat)
    (q : Packed Symbol arity Gamma) (r : Packed Symbol arity (sigma :: Gamma)),
    WindowTrace Symbol arity symbols S above (sigma :: Gamma) count (renamePacked (Renaming.weaken Gamma sigma) q) r →
    ∃ target : Packed Symbol arity Gamma, renamePacked (Renaming.weaken Gamma sigma) target = r ∧
      WindowTrace Symbol arity symbols S above Gamma count q target

def ActualTypedTraceWeakeningReflection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty) (sigma tau : Ty) (count : Nat)
    (q : AuxTerm Symbol arity Gamma tau) (r : AuxTerm Symbol arity (sigma :: Gamma) tau),
    WindowTypedTrace Symbol arity symbols S above (sigma :: Gamma) tau count (NumberedRewriteSyntax.rename q (Renaming.weaken Gamma sigma)) r →
    ∃ target : AuxTerm Symbol arity Gamma tau, NumberedRewriteSyntax.rename target (Renaming.weaken Gamma sigma) = r ∧
      WindowTypedTrace Symbol arity symbols S above Gamma tau count q target

def ActualTupleTraceWeakeningReflection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty) (sigma : Ty) (types : List Ty) (count : Nat)
    (base : AuxArguments Symbol arity Gamma types) (target : AuxArguments Symbol arity (sigma :: Gamma) types),
    WindowTupleTrace Symbol arity symbols S above (sigma :: Gamma) types count (renameArguments base (Renaming.weaken Gamma sigma)) target →
    ∃ result : AuxArguments Symbol arity Gamma types, renameArguments result (Renaming.weaken Gamma sigma) = target ∧
      WindowTupleTrace Symbol arity symbols S above Gamma types count base result

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningTargets
