module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocus
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedStepContexts

inductive Position where
  | lam
  | appFunction
  | ordinaryBase (index : Nat)
  | numberedBase (index : Nat)
  | numberedExtras (index : Nat)

structure TermFocus (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) where
  holeGamma : List Ty
  holeType : Ty
  context : TermContext n arity holeGamma holeType Gamma tau
  value : AuxTerm (Fin n) arity holeGamma holeType

structure ArgumentFocus (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty) where
  holeGamma : List Ty
  holeType : Ty
  context : ArgumentContext n arity holeGamma holeType Gamma types
  value : AuxTerm (Fin n) arity holeGamma holeType

/-- Structural index traversal. The actual caller supplies focus on a strictly shorter path. -/
def argumentFocusWith {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (visit : ∀ {tau},AuxTerm (Fin n) arity Gamma tau → Option (TermFocus n arity Gamma tau)) :
    {types : List Ty} → Nat → AuxArguments (Fin n) arity Gamma types → Option (ArgumentFocus n arity Gamma types)
  | [],_,.nil => none
  | _::_,0,.cons q rest => (visit q).map (fun f => ⟨f.holeGamma,f.holeType,.head f.context rest,f.value⟩)
  | _::_,index+1,.cons q rest => (argumentFocusWith visit index rest).map (fun f => ⟨f.holeGamma,f.holeType,.tail q f.context,f.value⟩)

def focus {n : Nat} {arity : Fin n → Nat} : (path : List Position) → {Gamma : List Ty} → {tau : Ty} →
    AuxTerm (Fin n) arity Gamma tau → Option (TermFocus n arity Gamma tau)
  | [],_,_,q => some ⟨_,_,.hole,q⟩
  | .lam::path,_,_,.lam body => (focus path body).map (fun f => ⟨f.holeGamma,f.holeType,.lam f.context,f.value⟩)
  | .appFunction::path,_,_,.app fn arg => (focus path fn).map (fun f => ⟨f.holeGamma,f.holeType,.appFunction f.context arg,f.value⟩)
  | .ordinaryBase index::path,_,_,.ordinary head base =>
      (argumentFocusWith (fun q => focus path q) index base).map (fun f => ⟨f.holeGamma,f.holeType,.ordinary head f.context,f.value⟩)
  | .numberedBase index::path,_,_,.numbered label head tau base types extras =>
      (argumentFocusWith (fun q => focus path q) index base).map (fun f => ⟨f.holeGamma,f.holeType,.numberedBase label head tau f.context types extras,f.value⟩)
  | .numberedExtras index::path,_,_,.numbered label head tau base types extras =>
      (argumentFocusWith (fun q => focus path q) index extras).map (fun f => ⟨f.holeGamma,f.holeType,.numberedExtras label head tau base types f.context,f.value⟩)
  | _::_,_,_,_ => none
termination_by path => path.length

def focusArguments {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
    (path : List Position) (index : Nat) (args : AuxArguments (Fin n) arity Gamma types) : Option (ArgumentFocus n arity Gamma types) :=
  argumentFocusWith (fun q => focus path q) index args

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocus
