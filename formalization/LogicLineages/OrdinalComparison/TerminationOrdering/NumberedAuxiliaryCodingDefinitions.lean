module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCoding
open Source Source.SourceMarkedSyntax Source.SourceTypedPorts NumberedRewriteSyntax NumberedRewriteReduction

inductive HeadCode (Symbol : Type) where
  | zero | succ
  | cases (result : Ty)
  | recursor (result : Ty)
  | application (domain result : Ty)
  | ranked (symbol : Symbol)
  deriving DecidableEq

def headCode {Symbol : Type} : Head Symbol → HeadCode Symbol
  | .zero => .zero
  | .succ => .succ
  | .cases tau => .cases tau
  | .recursor tau => .recursor tau
  | .application sigma tau => .application sigma tau
  | .ranked s => .ranked s

inductive Code (Symbol : Type) where
  | var (index : Nat)
  | lam (domain : Ty) (body : Code Symbol)
  | app (domain : Ty) (function argument : Code Symbol)
  | bottom (result : Ty)
  | ordinary (head : HeadCode Symbol) (base : Code Symbol)
  | numbered (label : Nat) (head : HeadCode Symbol) (result : Ty)
      (base : Code Symbol) (extraTypes : List Ty) (extras : Code Symbol)
  | argumentsNil
  | argumentsCons (type : Ty) (head tail : Code Symbol)
  deriving DecidableEq

mutual
def termCode {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Code Symbol
  | .var v => .var (variableIndex v)
  | @AuxTerm.lam _ _ _ sigma _ body => .lam sigma (termCode body)
  | @AuxTerm.app _ _ _ sigma _ q a => .app sigma (termCode q) (termCode a)
  | .bottom tau => .bottom tau
  | .ordinary f base => .ordinary (headCode f) (argumentsCode base)
  | .numbered k f tau base types extras => .numbered k (headCode f) tau (argumentsCode base) types (argumentsCode extras)
def argumentsCode {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} : AuxArguments Symbol arity Gamma types → Code Symbol
  | .nil => .argumentsNil
  | @AuxArguments.cons _ _ _ sigma _ q rest => .argumentsCons sigma (termCode q) (argumentsCode rest)
end

def packedCode {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (q : Packed Symbol arity Gamma) : Ty × Code Symbol := (q.1,termCode q.2)

def packedEqual {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (q r : Packed Symbol arity Gamma) : Bool := decide (packedCode q=packedCode r)

mutual
def maxLabel {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Nat
  | .var _ | .bottom _ => 0
  | .lam body => maxLabel body
  | .app q a => max (maxLabel q) (maxLabel a)
  | .ordinary _ base => argumentsMaxLabel base
  | .numbered k _ _ base _ extras => max k (max (argumentsMaxLabel base) (argumentsMaxLabel extras))
def argumentsMaxLabel {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} : AuxArguments Symbol arity Gamma types → Nat
  | .nil => 0
  | .cons q rest => max (maxLabel q) (argumentsMaxLabel rest)
end

mutual
def LabelsAtMost {Symbol : Type} {arity : Symbol → Nat} (L : Nat) {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Prop
  | .var _ | .bottom _ => True
  | .lam body => LabelsAtMost L body
  | .app q a => LabelsAtMost L q ∧ LabelsAtMost L a
  | .ordinary _ base => ArgumentLabelsAtMost L base
  | .numbered k _ _ base _ extras => k≤L ∧ ArgumentLabelsAtMost L base ∧ ArgumentLabelsAtMost L extras
def ArgumentLabelsAtMost {Symbol : Type} {arity : Symbol → Nat} (L : Nat) {Gamma types : List Ty} : AuxArguments Symbol arity Gamma types → Prop
  | .nil => True
  | .cons q rest => LabelsAtMost L q ∧ ArgumentLabelsAtMost L rest
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCoding
