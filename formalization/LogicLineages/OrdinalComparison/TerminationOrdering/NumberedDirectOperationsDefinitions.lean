module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionProof

@[expose] public section
/-! Actual argument append/opening and the remaining direct certificate operations.
Raw code fallbacks are total on malformed inputs; the required calibrations are
to the existing typed appendArguments/openNumbered/directTarget operations.
All output types, finite labels, retained head/base/extras and binder order stay
literal. No new rewrite or comparison rule is introduced.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperations
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryShift

def appendArgumentCode {Symbol : Type} : Code Symbol → Code Symbol → Code Symbol
  | .argumentsCons sigma q rest,last => .argumentsCons sigma q (appendArgumentCode rest last)
  | _,last => last

abbrev OpenData (Symbol : Type) := Nat × HeadCode Symbol × Ty × Ty × Code Symbol × List Ty × Code Symbol

def openCode {Symbol : Type} (p : OpenData Symbol) : Code Symbol :=
  .numbered p.1 p.2.1 p.2.2.2.1 (shiftCode 0 p.2.2.2.2.1) (p.2.2.2.2.2.1++[p.2.2.1])
    (appendArgumentCode (shiftCode 0 p.2.2.2.2.2.2) (.argumentsCons p.2.2.1 (.var 0) .argumentsNil))

def abstractionCode {Symbol : Type} : Code Symbol → Option (Code Symbol)
  | .numbered (k+1) head (.arrow sigma tau) base types extras =>
      some (.lam sigma (openCode (k,head,sigma,tau,base,types,extras)))
  | _ => none

def putCode {Symbol : Type} (label : Nat) (tau : Ty) : Code Symbol → Option (Code Symbol)
  | .ordinary head base => some (.numbered label head tau base [] .argumentsNil)
  | _ => none

def bottomCode {Symbol : Type} (tau : Ty) : Code Symbol → Option (Code Symbol)
  | .bottom _ => none
  | _ => some (.bottom tau)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperations
