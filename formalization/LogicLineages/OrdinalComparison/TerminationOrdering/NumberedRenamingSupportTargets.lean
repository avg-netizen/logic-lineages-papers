module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportTargets
open Source NumberedRewriteSyntax NumberedRenamingSupport

def ActualLiftRange : Prop := ∀ (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (sigma tau : Ty)
    (v : Variable (sigma :: Delta) tau),
    liftPredicate (rangePredicate rho) v ↔ rangePredicate (Renaming.lift rho) v

def ActualTermSupportImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (rho : Renaming Gamma Delta) (tau : Ty) (q : AuxTerm Symbol arity Delta tau),
    supports (rangePredicate rho) q ↔ ∃ source : AuxTerm Symbol arity Gamma tau, NumberedRewriteSyntax.rename source rho = q

def ActualArgumentSupportImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (rho : Renaming Gamma Delta) (types : List Ty) (args : AuxArguments Symbol arity Delta types),
    supportsArguments (rangePredicate rho) args ↔
      ∃ source : AuxArguments Symbol arity Gamma types, renameArguments source rho = args

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportTargets
