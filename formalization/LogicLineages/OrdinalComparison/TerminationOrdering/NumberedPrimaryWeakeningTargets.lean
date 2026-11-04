module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryWeakening

def ActualTermRenameAsSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    NumberedRewriteSyntax.rename q rho = substitute q (fun v => AuxTerm.var (rho v))

def ActualArgumentRenameAsSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    renameArguments args rho = substituteArguments args (fun v => AuxTerm.var (rho v))

def ActualPrimaryWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S Gamma : List Ty) (sigma : Ty) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r ↔
    WindowPrimary Symbol arity symbols S (sigma :: Gamma)
      (renamePacked (Renaming.weaken Gamma sigma) q) (renamePacked (Renaming.weaken Gamma sigma) r)

def ActualArgumentPrimaryWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S Gamma : List Ty) (sigma : Ty) (types : List Ty) (args target : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types args target ↔
    WindowArgumentPrimary Symbol arity symbols S (sigma :: Gamma) types
      (renameArguments args (Renaming.weaken Gamma sigma)) (renameArguments target (Renaming.weaken Gamma sigma))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningTargets
