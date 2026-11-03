module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecoding
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration

def decodeHead {Symbol : Type} : HeadCode Symbol → Head Symbol
  | .zero => .zero
  | .succ => .succ
  | .cases tau => .cases tau
  | .recursor tau => .recursor tau
  | .application sigma tau => .application sigma tau
  | .ranked s => .ranked s

def decodeVariable (Gamma : List Ty) (tau : Ty) (index : Nat) : Option (Variable Gamma tau) :=
  match Gamma,index with
  | [],_ => none
  | sigma::_,0 => if h : sigma=tau then some (h ▸ Variable.here) else none
  | _::rest,index+1 => (decodeVariable rest tau index).map Variable.there

mutual
def decodeTerm {Symbol : Type} (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty) : Code Symbol → Option (AuxTerm Symbol arity Gamma tau)
  | .var i => (decodeVariable Gamma tau i).map AuxTerm.var
  | .lam sigma body =>
    match tau with
    | .ground => none
    | .arrow domain result =>
      if h : sigma=domain then
        (decodeTerm arity (domain::Gamma) result body).map AuxTerm.lam
      else none
  | .app sigma q a => do
    let function ← decodeTerm arity Gamma (.arrow sigma tau) q
    let argument ← decodeTerm arity Gamma sigma a
    pure (.app function argument)
  | .bottom result => if h : result=tau then some (.bottom tau) else none
  | .ordinary head base =>
    if h : headResult (decodeHead head)=tau then
      (decodeArguments arity Gamma (headArguments arity (decodeHead head)) base).map
        (fun args => h ▸ AuxTerm.ordinary (decodeHead head) args)
    else none
  | .numbered k head result base types extras =>
    if h : result=tau then do
      let args ← decodeArguments arity Gamma (headArguments arity (decodeHead head)) base
      let extraArgs ← decodeArguments arity Gamma types extras
      pure (.numbered k (decodeHead head) tau args types extraArgs)
    else none
  | .argumentsNil | .argumentsCons _ _ _ => none

def decodeArguments {Symbol : Type} (arity : Symbol → Nat) (Gamma types : List Ty) : Code Symbol → Option (AuxArguments Symbol arity Gamma types)
  | .argumentsNil => match types with
    | [] => some .nil
    | _::_ => none
  | .argumentsCons sigma q rest => match types with
    | [] => none
    | domain::tail => if h : sigma=domain then do
        let value ← decodeTerm arity Gamma domain q
        let values ← decodeArguments arity Gamma tail rest
        pure (.cons value values)
      else none
  | _ => none
end

def decodePacked {Symbol : Type} (arity : Symbol → Nat) (Gamma : List Ty) (c : Ty × Code Symbol) : Option (Packed Symbol arity Gamma) :=
  (decodeTerm arity Gamma c.1 c.2).map (fun q => ⟨c.1,q⟩)

def classCandidates {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) : List (Packed Symbol arity Gamma) :=
  (classCodes symbols S q).filterMap (decodePacked arity Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecoding
