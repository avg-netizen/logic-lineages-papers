module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

def ActualTermRoundTrip : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
  decodeTerm arity Gamma tau (termCode q)=some q

def ActualArgumentsRoundTrip : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty) (args : AuxArguments Symbol arity Gamma types),
  decodeArguments arity Gamma types (argumentsCode args)=some args

def ActualTermDecodeSound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty) (c : Code Symbol) (q : AuxTerm Symbol arity Gamma tau),
  decodeTerm arity Gamma tau c=some q → termCode q=c

def ActualArgumentsDecodeSound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty) (c : Code Symbol) (args : AuxArguments Symbol arity Gamma types),
  decodeArguments arity Gamma types c=some args → argumentsCode args=c

def ActualPackedRoundTrip : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (q : Packed Symbol arity Gamma),
  decodePacked arity Gamma (packedCode q)=some q

def ActualCandidateCoverage : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  InUniverse symbols S q.2 → WindowPrimary Symbol arity symbols S Gamma q r → r∈classCandidates symbols S q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingTargets
