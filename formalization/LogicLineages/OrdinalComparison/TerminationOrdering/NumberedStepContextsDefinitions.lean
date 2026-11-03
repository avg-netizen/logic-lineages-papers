module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContexts
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction

mutual
inductive TermContext (n : Nat) (arity : Fin n → Nat) (holeGamma : List Ty) (holeType : Ty) : List Ty → Ty → Type where
  | hole : TermContext n arity holeGamma holeType holeGamma holeType
  | lam {Gamma sigma tau} (body : TermContext n arity holeGamma holeType (sigma::Gamma) tau) :
      TermContext n arity holeGamma holeType Gamma (.arrow sigma tau)
  | appFunction {Gamma sigma tau} (fn : TermContext n arity holeGamma holeType Gamma (.arrow sigma tau))
      (arg : AuxTerm (Fin n) arity Gamma sigma) : TermContext n arity holeGamma holeType Gamma tau
  | ordinary {Gamma} (f : Head (Fin n)) (base : ArgumentContext n arity holeGamma holeType Gamma (headArguments arity f)) :
      TermContext n arity holeGamma holeType Gamma (headResult f)
  | numberedBase {Gamma} (label : Nat) (f : Head (Fin n)) (tau : Ty)
      (base : ArgumentContext n arity holeGamma holeType Gamma (headArguments arity f)) (types : List Ty)
      (extras : AuxArguments (Fin n) arity Gamma types) : TermContext n arity holeGamma holeType Gamma tau
  | numberedExtras {Gamma} (label : Nat) (f : Head (Fin n)) (tau : Ty)
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f)) (types : List Ty)
      (extras : ArgumentContext n arity holeGamma holeType Gamma types) : TermContext n arity holeGamma holeType Gamma tau
inductive ArgumentContext (n : Nat) (arity : Fin n → Nat) (holeGamma : List Ty) (holeType : Ty) : List Ty → List Ty → Type where
  | head {Gamma sigma types} (q : TermContext n arity holeGamma holeType Gamma sigma)
      (rest : AuxArguments (Fin n) arity Gamma types) : ArgumentContext n arity holeGamma holeType Gamma (sigma::types)
  | tail {Gamma sigma types} (q : AuxTerm (Fin n) arity Gamma sigma)
      (rest : ArgumentContext n arity holeGamma holeType Gamma types) : ArgumentContext n arity holeGamma holeType Gamma (sigma::types)
end

mutual
def plug {n : Nat} {arity : Fin n → Nat} {holeGamma : List Ty} {holeType : Ty} {Gamma : List Ty} {tau : Ty}
    (context : TermContext n arity holeGamma holeType Gamma tau) (q : AuxTerm (Fin n) arity holeGamma holeType) : AuxTerm (Fin n) arity Gamma tau :=
  match context with
  | .hole => q
  | .lam body => .lam (plug body q)
  | .appFunction fn arg => .app (plug fn q) arg
  | .ordinary f base => .ordinary f (plugArguments base q)
  | .numberedBase label f tau base types extras => .numbered label f tau (plugArguments base q) types extras
  | .numberedExtras label f tau base types extras => .numbered label f tau base types (plugArguments extras q)

def plugArguments {n : Nat} {arity : Fin n → Nat} {holeGamma : List Ty} {holeType : Ty} {Gamma types : List Ty}
    (context : ArgumentContext n arity holeGamma holeType Gamma types) (q : AuxTerm (Fin n) arity holeGamma holeType) : AuxArguments (Fin n) arity Gamma types :=
  match context with
  | .head first rest => .cons (plug first q) rest
  | .tail first rest => .cons first (plugArguments rest q)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContexts
