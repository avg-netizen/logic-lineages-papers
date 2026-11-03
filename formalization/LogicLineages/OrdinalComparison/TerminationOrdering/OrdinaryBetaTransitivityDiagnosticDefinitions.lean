module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTransitivityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalCompositionFramesProof

@[expose] public section
/-! A concrete diagnostic in the ACTUAL original Term domain, not an arbitrary
marked-source generalization. All displayed P,T,U are literal source terms.
This file specifies a candidate; no nonderivability claim follows from it. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnostic
open Source Source.SourceMarkedSyntax RecursiveComparison

abbrev arity : Nat → Nat | 2 => 1 | 3 => 2 | _ => 0
def above (f g : Nat) : Prop := g<f
abbrev OriginalGround (Gamma : List Ty) := Term Nat arity Gamma .ground
abbrev Ground := MarkedTerm Nat arity [] .ground

def zOriginal (Gamma : List Ty) : OriginalGround Gamma := .ranked 0 (fun i => Fin.elim0 i)
def hOriginal (Gamma : List Ty) : OriginalGround Gamma := .ranked 1 (fun i => Fin.elim0 i)
def kOriginal : OriginalGround [] := .ranked 2 (fun _ => hOriginal [])
def bodyOriginal : OriginalGround [.ground] :=
  .ranked 3 (Fin.cases (.var .here) (fun _ => zOriginal [.ground]))
def pOriginal : OriginalGround [] := .app (.lam bodyOriginal) kOriginal
def tOriginal : OriginalGround [] :=
  .ranked 3 (Fin.cases kOriginal (fun _ => zOriginal []))
def uOriginal : OriginalGround [] := .ranked 3 (fun _ => hOriginal [])

def z : Ground := embed (zOriginal [])
def h : Ground := embed (hOriginal [])
def k : Ground := embed kOriginal
def p : Ground := embed pOriginal
def t : Ground := embed tOriginal
def u : Ground := embed uOriginal
def applicationBase : Arguments Nat arity [] [.arrow .ground .ground,.ground] :=
  .cons (.lam (embed bodyOriginal)) (.cons k .nil)
def q : Ground := .marked (.application .ground .ground) .ground applicationBase [] .nil
def s : Ground := .ordinary (.ranked 3) (.cons q (.cons z .nil))
def markedS : Ground := .marked (.ranked 3) .ground (.cons q (.cons z .nil)) [] .nil

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnostic
