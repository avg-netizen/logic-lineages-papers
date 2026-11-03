module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryExchange

def ActualExchangeErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  Exchange Symbol arity symbols S Gamma q r → WindowPrimary Symbol arity symbols S Gamma q r

def ActualExchangeSymmetry : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  Exchange Symbol arity symbols S Gamma q r → Exchange Symbol arity symbols S Gamma r q

def ActualPrimaryClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  Chain (Exchange Symbol arity symbols S Gamma) q r ↔ WindowPrimary Symbol arity symbols S Gamma q r

def ActualArgumentClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (Gamma types : List Ty) (args target : AuxArguments Symbol arity Gamma types),
  Chain (ArgumentExchange Symbol arity symbols S Gamma types) args target ↔ WindowArgumentPrimary Symbol arity symbols S Gamma types args target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeTargets
