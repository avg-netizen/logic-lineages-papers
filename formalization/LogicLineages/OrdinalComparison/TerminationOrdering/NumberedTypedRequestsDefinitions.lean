module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableDecoderPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequests
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

inductive Request (n : Nat) where
  | term (Gamma : List Ty) (tau : Ty) (code : Code (Fin n))
  | arguments (Gamma types : List Ty) (code : Code (Fin n))

def valid {n : Nat} (arity : Fin n → Nat) : Request n → Bool
  | .term Gamma tau code => (decodeTerm arity Gamma tau code).isSome
  | .arguments Gamma types code => (decodeArguments arity Gamma types code).isSome

def expand {n : Nat} (arity : Fin n → Nat) : Request n → Option (List (Request n))
  | .term Gamma tau (.var index) => if Gamma[index]?=some tau then some [] else none
  | .term Gamma tau (.lam sigma body) => match tau with
    | .ground => none
    | .arrow domain result => if sigma=domain then some [.term (domain::Gamma) result body] else none
  | .term Gamma tau (.app sigma q a) => some [.term Gamma (.arrow sigma tau) q,.term Gamma sigma a]
  | .term _ tau (.bottom result) => if result=tau then some [] else none
  | .term Gamma tau (.ordinary head base) =>
    if headResult (decodeHead head)=tau then some [.arguments Gamma (headArguments arity (decodeHead head)) base] else none
  | .term Gamma tau (.numbered _ head result base types extras) =>
    if result=tau then some [.arguments Gamma (headArguments arity (decodeHead head)) base,.arguments Gamma types extras] else none
  | .term _ _ .argumentsNil | .term _ _ (.argumentsCons _ _ _) => none
  | .arguments _ [] .argumentsNil => some []
  | .arguments _ (_::_) .argumentsNil => none
  | .arguments _ [] (.argumentsCons _ _ _) => none
  | .arguments Gamma (domain::tail) (.argumentsCons sigma q rest) =>
    if sigma=domain then some [.term Gamma domain q,.arguments Gamma tail rest] else none
  | .arguments _ _ _ => none

def expandedValid {n : Nat} (arity : Fin n → Nat) (request : Request n) : Bool :=
  match expand arity request with
  | none => false
  | some children => children.all (valid arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequests
