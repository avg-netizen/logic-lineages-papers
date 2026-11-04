module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimaryWeakening
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths

def ActualPackedTraceRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r →
    WindowTrace Symbol arity symbols S above Delta count (renamePacked rho q) (renamePacked rho r)

def ActualTypedTraceRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (tau : Ty) (count : Nat)
    (q r : AuxTerm Symbol arity Gamma tau),
    WindowTypedTrace Symbol arity symbols S above Gamma tau count q r →
    WindowTypedTrace Symbol arity symbols S above Delta tau count (NumberedRewriteSyntax.rename q rho) (NumberedRewriteSyntax.rename r rho)

def ActualTupleTraceRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (types : List Ty) (count : Nat)
    (base target : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma types count base target →
    WindowTupleTrace Symbol arity symbols S above Delta types count (renameArguments base rho) (renameArguments target rho)

def ActualCountedQuotientRenaming : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (q r : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    ∀ count : Nat, CountedPath (QuotientEdge n arity symbols S above Gamma) count
      (representativeCode symbols S q) (representativeCode symbols S r) →
    CountedPath (QuotientEdge n arity symbols S above Delta) count
      (representativeCode symbols S (renamePacked rho q)) (representativeCode symbols S (renamePacked rho r))

def ActualPositiveQuotientRenaming : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (q r : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S q) (representativeCode symbols S r) →
    PositivePath (QuotientEdge n arity symbols S above Delta)
      (representativeCode symbols S (renamePacked rho q)) (representativeCode symbols S (renamePacked rho r))

def ActualRepresentativeRenaming : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 → representativeCode symbols S q = representativeCode symbols S r →
    representativeCode symbols S (renamePacked rho q) = representativeCode symbols S (renamePacked rho r)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceRenamingTargets
