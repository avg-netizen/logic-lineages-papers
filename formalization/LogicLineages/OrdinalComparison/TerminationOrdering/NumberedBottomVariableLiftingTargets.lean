module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableLiftingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableLiftingTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution
open NumberedBottomVariable NumberedWindowReduction NumberedWindowEquivalence
open NumberedPrimaryExchange NumberedWindowTraces

/-- Every actual substituted raw edge has an original raw preimage edge.
No universe, subtype-closure, or injectivity hypothesis is imposed. -/
def ActualStepInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (tau : Ty)
      (q : AuxTerm Symbol arity Gamma tau) (r : AuxTerm Symbol arity Delta tau),
    WindowStep Symbol arity symbols S above Delta tau (substitute q theta) r →
    ∃ q' : AuxTerm Symbol arity Gamma tau,
      WindowStep Symbol arity symbols S above Gamma tau q q' ∧ substitute q' theta = r

def ActualArgumentStepInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (types : List Ty)
      (base : AuxArguments Symbol arity Gamma types) (target : AuxArguments Symbol arity Delta types),
    WindowArgumentStep Symbol arity symbols S above Delta types (substituteArguments base theta) target →
    ∃ source : AuxArguments Symbol arity Gamma types,
      WindowArgumentStep Symbol arity symbols S above Gamma types base source ∧
      substituteArguments source theta = target

/-- Packed exchange retains actual head guards, types, and occurrence counts. -/
def ActualExchangeInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (q : Packed Symbol arity Gamma) (r : Packed Symbol arity Delta),
    Exchange Symbol arity symbols S Delta (substitutePacked theta q) r →
    ∃ q' : Packed Symbol arity Gamma,
      Exchange Symbol arity symbols S Gamma q q' ∧ substitutePacked theta q' = r

def ActualArgumentExchangeInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (types : List Ty)
      (base : AuxArguments Symbol arity Gamma types) (target : AuxArguments Symbol arity Delta types),
    ArgumentExchange Symbol arity symbols S Delta types (substituteArguments base theta) target →
    ∃ source : AuxArguments Symbol arity Gamma types,
      ArgumentExchange Symbol arity symbols S Gamma types base source ∧
      substituteArguments source theta = target

def ActualPrimaryInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (q : Packed Symbol arity Gamma) (r : Packed Symbol arity Delta),
    WindowPrimary Symbol arity symbols S Delta (substitutePacked theta q) r →
    ∃ q' : Packed Symbol arity Gamma,
      WindowPrimary Symbol arity symbols S Gamma q q' ∧ substitutePacked theta q' = r

/-- Raw-edge count is preserved, including zero-count primary segments and
positive genuine self-edges. No stuttering quotient is substituted. -/
def ActualTraceInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (count : Nat)
      (q : Packed Symbol arity Gamma) (r : Packed Symbol arity Delta),
    WindowTrace Symbol arity symbols S above Delta count (substitutePacked theta q) r →
    ∃ q' : Packed Symbol arity Gamma,
      WindowTrace Symbol arity symbols S above Gamma count q q' ∧ substitutePacked theta q' = r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableLiftingTargets
