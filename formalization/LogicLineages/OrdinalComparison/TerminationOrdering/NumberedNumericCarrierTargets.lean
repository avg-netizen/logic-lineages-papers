module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericCarrier

def ActualUniverseTest : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
  universeTest symbols S q=true ↔ InUniverse symbols S q

def ActualArgumentsUniverseTest : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S Gamma types : List Ty) (args : AuxArguments Symbol arity Gamma types),
  argumentsUniverseTest symbols S args=true ↔
    auxArgumentTypesAllowed (fun tau => tau∈S) args ∧ auxArgumentsAllowed (HeadInWindow arity symbols S) args

def ActualNumericUniverseDecode : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) (q : Packed (Fin n) arity Gamma),
  decodeUniverse n arity symbols S Gamma value=some q ↔ packedNumber q=value ∧ InUniverse symbols S q.2

def ActualRawCarrierTest : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat),
  rawCarrierTest n arity symbols S Gamma value=true ↔ ∃ q : Packed (Fin n) arity Gamma,InUniverse symbols S q.2 ∧ packedNumber q=value

def ActualCanonicalCarrierTest : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (value : Nat),
  canonicalCarrierTest n arity symbols S Gamma value=true ↔
    ∃ q : Packed (Fin n) arity Gamma,InUniverse symbols S q.2 ∧ representativeCode symbols S q=value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierTargets
