module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice SupportProof

theorem internalConservation : Targets.InternalConservation := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx lines history out index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (run itag ptag lines (.succ history) lines index fuel) (state ptag (.succ out) .zero)
  have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  obtain ⟨hconv⟩ := ConversionProof.internalBoundConversion v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx lines (.succ history) index fuel
  obtain ⟨hprop⟩ := InductionProof.lengthProperty p itag ltag ptag ctag v l a x hi hl hp hc lines index fuel
  have hsome := Derivation.mp (someElim itag ltag ptag lines history out index fuel) hprop
  have hin := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hconv)) h
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hsome) hin))⟩

theorem internalEmptyConservation : Targets.InternalEmptyConservation := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx lines out index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (run itag ptag lines (.succ .zero) lines index fuel) (state ptag (.succ out) .zero)
  have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  obtain ⟨hcns⟩ := internalConservation v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx lines .zero out index fuel
  have hlen := Hilbert.Local.mp (.base hcns) h
  obtain ⟨hz⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
  have he := localUnary (.add (.var 0) (liftTerm (lengthCall ltag lines))) _ _ (Hilbert.Local.base (Gamma := [H]) hz)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at he
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hlen
    (localTrans _ _ _ he (.base (zeroLeft (lengthCall ltag lines))))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.Proof
