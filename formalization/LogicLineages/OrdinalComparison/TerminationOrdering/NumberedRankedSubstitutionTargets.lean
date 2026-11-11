module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction
open NumberedWindowTraces NumberedPrimarySubstitution NumberedFiniteUniverse NumberedUniverseBindingTargets
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedVariableCount

def ActualRankedStepSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r →
    (substitute q theta = substitute r theta ∧ variableCount r < variableCount q) ∨
    WindowStep Symbol arity symbols S above Delta tau (substitute q theta) (substitute r theta)

def ActualRankedArgumentStepSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (types : List Ty) (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types base target →
    (substituteArguments base theta = substituteArguments target theta ∧
      argumentVariableCount target < argumentVariableCount base) ∨
    WindowArgumentStep Symbol arity symbols S above Delta types
      (substituteArguments base theta) (substituteArguments target theta)

/-- If every transformed raw edge is erased, the original rank pays for every
original raw edge. Otherwise the actual transformed trace retains its edges. -/
def ActualRankedPackedTraceSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r →
    ∃ m : Nat, m ≤ count ∧
      WindowTrace Symbol arity symbols S above Delta m (substitutePacked theta q) (substitutePacked theta r) ∧
      (m = 0 → packedVariableCount r + count ≤ packedVariableCount q)

/-- Exact original positive quotient substitution scope, strengthened only in
the equality alternative. This does not assert all-type weakening or C/Acc. -/
def ActualRankedPositiveQuotientSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S q) (representativeCode symbols S r) →
    (representativeCode symbols S (substitutePacked theta q) =
      representativeCode symbols S (substitutePacked theta r) ∧ packedVariableCount r < packedVariableCount q) ∨
    PositivePath (QuotientEdge n arity symbols S above Delta)
      (representativeCode symbols S (substitutePacked theta q))
      (representativeCode symbols S (substitutePacked theta r))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionTargets
