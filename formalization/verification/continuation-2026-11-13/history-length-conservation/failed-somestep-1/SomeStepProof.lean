module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SomeStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice SupportProof
open HistoryKernel.TransitionEquationsProof HistoryKernel.EntryProof

theorem someCons {n ctx : Nat} (p : Program n) (itag ltag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail history out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag ptag tail index fuel)
        (someRelation itag ltag ptag (HistoryLookup.consCall ctag line tail) history out index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let kt := itag+stepTag iterationBase+1
  let code := HistoryLookup.consCall ctag line tail
  let P := property itag ltag ptag tail index fuel
  let H := Formula.equal (run itag ptag (lengthCall ltag code) (.succ history) code index fuel) (state ptag (.succ out) .zero)
  let O := optionValue kt v l a x index fuel history line
  let N := newHistory (someTag kt v l a x) history line
  let C := HistoryDispatcher.dispatcherCall (dispatcherTag kt v l a x) index fuel history line
  let Q := Formula.equal (lengthCall ltag out) (.add (lengthCall ltag history) (lengthCall ltag code))
  let Z := Formula.equal O .zero
  let S := Formula.conj (.equal C (.succ .zero)) (.equal O (.succ N))
  obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx line tail
  obtain ⟨hs⟩ := ConsRunProof.someCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) history line tail index fuel
  have hstep : Derivation T (.equal (run itag ptag (lengthCall ltag code) (.succ history) code index fuel)
      (run itag ptag (lengthCall ltag tail) O tail index fuel)) :=
    Hilbert.Local.finish (localTrans _ _ _
      (StationaryProof.iterationCount itag _ _ (state ptag (.succ history) code) index fuel (.base hlen)) (.base hs))
  have zeroCase : Hilbert.Local T ctx [H,P] (.imp Z Q) := by
    have hz : Hilbert.Local T ctx [Z,H,P] Z := .hypothesis List.mem_cons_self
    have hh : Hilbert.Local T ctx [Z,H,P] H := .hypothesis (by simp)
    have ih : Hilbert.Local T ctx [Z,H,P] P := .hypothesis (by simp)
    have hrun := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hstep)) hh
    have ho := StepSupportProof.optionCongruence itag ptag (lengthCall ltag tail) O .zero tail index fuel hz
    have hnone := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ ho) hrun
    have hn := Hilbert.Local.mp (.base (noneElim itag ltag ptag tail out index fuel)) ih
    exact Hilbert.Local.discharge (Hilbert.Local.explosion Q hnone hn)
  have someCase : Hilbert.Local T ctx [H,P] (.imp S Q) := by
    have hS : Hilbert.Local T ctx [S,H,P] S := .hypothesis List.mem_cons_self
    have ho : Hilbert.Local T ctx [S,H,P] (.equal O (.succ N)) := .mp (.base (.logical (.andRight _ _))) hS
    have hh : Hilbert.Local T ctx [S,H,P] H := .hypothesis (by simp)
    have ih : Hilbert.Local T ctx [S,H,P] P := .hypothesis (by simp)
    have hrun := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hstep)) hh
    have hcng := StepSupportProof.optionCongruence itag ptag (lengthCall ltag tail) O (.succ N) tail index fuel ho
    have hsome := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hcng) hrun
    have hlength := Hilbert.Local.mp (.mp (.base (someElim itag ltag ptag tail N out index fuel)) ih) hsome
    obtain ⟨hnew⟩ := StepSupportProof.newHistoryLength p kt ltag v l a x (IdleProof.kernelInstalled p itag v l a x hi) hl history line
    have hsum1 := localUnary (.add (.var 0) (liftTerm (lengthCall ltag tail))) _ _ (Hilbert.Local.base (Gamma := [S,H,P]) hnew)
    simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hsum1
    have hsum2 := localTrans _ _ _ hsum1 (.base (successorLeft (lengthCall ltag history) (lengthCall ltag tail)))
    have hrhs1 := localUnary (.add (liftTerm (lengthCall ltag history)) (.var 0)) _ _ (Hilbert.Local.base (Gamma := [S,H,P]) hlen)
    simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hrhs1
    have hrhs := localTrans _ _ _ hrhs1 (.base (.arithmetic (.addSucc (lengthCall ltag history) (lengthCall ltag tail))))
    exact Hilbert.Local.discharge (localTrans _ _ _ hlength (localTrans _ _ _ hsum2 (HistoryOrder.StepProof.localSym _ _ hrhs)))
  obtain ⟨hgraph⟩ := HistoryKernel.OptionProof.optionGraph p kt v l a x (IdleProof.kernelInstalled p itag v l a x hi) index fuel history line
  have hout : Hilbert.Local T ctx [H,P] Q := .mp (.mp (.mp (.base (.logical (.orElim Z S Q))) zeroCase) someCase) (.base hgraph)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SomeStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SomeStepProof
