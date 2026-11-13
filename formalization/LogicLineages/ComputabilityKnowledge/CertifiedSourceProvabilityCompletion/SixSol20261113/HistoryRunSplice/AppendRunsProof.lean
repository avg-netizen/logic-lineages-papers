module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.AppendRunsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset

theorem internalAppendRuns : Targets.InternalAppendRuns := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx left right outLeft outRight index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let code := HistoryAppend.appendCall atag left right
  let HL := Formula.equal (run itag ptag left (.succ .zero) left index fuel) (state ptag (.succ outLeft) .zero)
  let HR := Formula.equal (run itag ptag right (.succ .zero) right index fuel) (state ptag (.succ outRight) .zero)
  have hleft : Hilbert.Local T ctx [HR,HL] HL := .hypothesis (by simp)
  have hright : Hilbert.Local T ctx [HR,HL] HR := .hypothesis List.mem_cons_self
  obtain ⟨hpre⟩ := PrefixProof.internalPrefixSplice v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx left right .zero outLeft index fuel
  have hprefix := Hilbert.Local.mp (.base hpre) hleft
  obtain ⟨hsuf⟩ := HistoryIteratorSuffix.IterationProof.internalIteratorSuffix v l a x n p itag atag ptag ctag hi ha hp hc ctx right index fuel .zero outLeft right outRight .zero
  have hsecond := Hilbert.Local.mp (.base hsuf) hright
  obtain ⟨happ0⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx outLeft
  have hop := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := [HR,HL]) happ0)
  have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ right (.succ outLeft) right hop (.base (.logical (.reflexive right)))
  have hstart := StationaryProof.iterationState itag right _ _ index fuel hstate
  have hsecond' := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hstart) hsecond
  obtain ⟨hcvR⟩ := ConversionProof.internalBoundConversion v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx right (.succ outLeft) index fuel
  have hshort := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hcvR)) hsecond'
  obtain ⟨hf⟩ := ConversionProof.fusionAt p itag (HistoryKernel.kernel v l a x) hi (lengthCall ltag left) (lengthCall ltag right) (state ptag (.succ .zero) code) index fuel
  have hmid := StationaryProof.iterationState itag (lengthCall ltag right) _ _ index fuel hprefix
  have hsum := localTrans _ _ _ (.base hf) (localTrans _ _ _ hmid hshort)
  obtain ⟨hdata⟩ := LengthDataProof.lengthData n p ltag atag droptag ctag hl ha hdrop hc ctx left right .zero
  have hlen : Derivation T (.equal (lengthCall ltag code) (.add (lengthCall ltag left) (lengthCall ltag right))) :=
    .mp (.logical (.andRight _ _)) (.mp (.logical (.andRight _ _)) hdata)
  have hcount := StationaryProof.iterationCount (T := T) (G := [HR,HL]) itag _ _ (state ptag (.succ .zero) code) index fuel (.base hlen)
  obtain ⟨hcvt⟩ := ConversionProof.internalBoundConversion v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx code (.succ .zero) index fuel
  have hout := localTrans _ _ _ (.base hcvt) (localTrans _ _ _ hcount hsum)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.AppendRunsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.AppendRunsProof
