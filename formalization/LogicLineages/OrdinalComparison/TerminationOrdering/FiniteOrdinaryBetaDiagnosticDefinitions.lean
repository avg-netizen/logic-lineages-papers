module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesProof

@[expose] public section
/-! The SAME diagnostic with an ACTUAL FOUR-ELEMENT ranked signature.
No infinite signature, well-foundedness assumption or oracle is hidden. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnostic
open Source Source.SourceMarkedSyntax RecursiveComparison

abbrev arity (i : Fin 4) : Nat := OrdinaryBetaTransitivityDiagnostic.arity i.val
def above (f g : Fin 4) : Prop := g.val<f.val
abbrev OriginalGround (Gamma : List Ty) := Term (Fin 4) arity Gamma .ground
abbrev Ground := MarkedTerm (Fin 4) arity [] .ground

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
def applicationBase : Arguments (Fin 4) arity [] [.arrow .ground .ground,.ground] :=
  .cons (.lam (embed bodyOriginal)) (.cons k .nil)
def q : Ground := .marked (.application .ground .ground) .ground applicationBase [] .nil
def s : Ground := .ordinary (.ranked 3) (.cons q (.cons z .nil))
def markedS : Ground := .marked (.ranked 3) .ground (.cons q (.cons z .nil)) [] .nil

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnostic
