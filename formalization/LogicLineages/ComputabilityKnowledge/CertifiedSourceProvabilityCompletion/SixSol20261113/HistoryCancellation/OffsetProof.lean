module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SeparationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OffsetProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof

def low {ctx : Nat} (a b : Term ctx) : Term ctx := .add (.mul b b) a
def high {ctx : Nat} (a b : Term ctx) : Term ctx := .add (.add (.mul a a) a) b

noncomputable def lowerSame {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (a b c d : Term ctx) (hm : Hilbert.Local T ctx G (.equal b d))
    (hv : Hilbert.Local T ctx G (.equal (low a b) (low c d))) :
    Hilbert.Local T ctx G (.equal a c) := by
  have hc := localUnary (.add (.mul (.var 0) (.var 0)) (liftTerm c)) _ _ hm
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hv (HistoryOrder.StepProof.localSym _ _ hc)
  exact .mp (.base (ArithmeticProof.left a c (.mul b b))) he

noncomputable def upperSame {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (a b c d : Term ctx) (hm : Hilbert.Local T ctx G (.equal a c))
    (hv : Hilbert.Local T ctx G (.equal (high a b) (high c d))) :
    Hilbert.Local T ctx G (.equal b d) := by
  have hc := localUnary (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (liftTerm d)) _ _ hm
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hv (HistoryOrder.StepProof.localSym _ _ hc)
  exact .mp (.base (ArithmeticProof.left b d (.add (.mul a a) a))) he

/-- A cross-half collision would put the lower offset at least at its major. -/
noncomputable def crossOffset {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (a b c d : Term ctx) (hm : Hilbert.Local T ctx G (.equal b c))
    (hv : Hilbert.Local T ctx G (.equal (low a b) (high c d))) :
    Hilbert.Local T ctx G (weakBound b a) := by
  have hc := localUnary (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (liftTerm d)) _ _ hm
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hv (HistoryOrder.StepProof.localSym _ _ hc)
  have ha := localTrans _ _ _ he (.base (addAssoc (T := T) (.mul b b) b d))
  have hoff : Hilbert.Local T ctx G (.equal a (.add b d)) :=
    .mp (.base (ArithmeticProof.left a (.add b d) (.mul b b))) ha
  exact .mp (.base (weakIntro b a d)) hoff

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OffsetProof
