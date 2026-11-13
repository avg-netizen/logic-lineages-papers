module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ReferenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice

theorem internalReferences : Targets.InternalReferences := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag rtag hi hl ha hp hc hd hdrop hr ctx context phi psi imp ant tailI tailA index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let HI := implicationHistory atag ptag ctag context phi psi tailI
  let HA := antecedentHistory ptag ctag context phi tailA
  let EI := implicationEntry atag ptag ctag context phi psi
  let EA := antecedentEntry ptag context phi
  let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
  have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have hA : Hilbert.Local T ctx [H] (.equal (run itag ptag ant (.succ .zero) ant index fuel) (state ptag (.succ HA) .zero)) :=
    .mp (.base (.logical (.andRight _ _))) h
  obtain ⟨hcns⟩ := HistoryLengthConservation.Proof.internalEmptyConservation v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx ant HA index fuel
  have hlen : Hilbert.Local T ctx [H] (.equal (lengthCall ltag HA) (lengthCall ltag ant)) := .mp (.base hcns) hA
  obtain ⟨hshift⟩ := HistoryLengthOffset.OffsetProof.internalRightLookupOffset n p ltag atag rtag ctag hl ha hr hc ctx HA HI .zero
  obtain ⟨hzeroI⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p rtag ctag hr hc ctx EI tailI
  obtain ⟨hzeroA⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p rtag ctag hr hc ctx EA tailA
  have hindex : Hilbert.Local T ctx [H] (.equal (lengthCall ltag ant) (.add (lengthCall ltag HA) .zero)) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hlen)
      (.base (Support.equalitySymmetry _ _ (.arithmetic (.addZero (lengthCall ltag HA)))))
  have hlook := HistoryLengthOffset.SelectProof.countCongruence rtag _ _
    (HistoryAppend.appendCall atag HA HI) (HistoryAppend.appendCall atag HA HI) hindex (.base (.logical (.reflexive _)))
  have hfirst := localTrans _ _ _ hlook (localTrans _ _ _ (.base hshift) (.base hzeroI))
  obtain ⟨hpres⟩ := HistoryAppend.PreserveProof.internalPreserveSome n p atag rtag ha hr ctx .zero HA HI EA
  have hsecond := Derivation.mp hpres hzeroA
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (.logical (.andIntro _ _))) hfirst) (.base hsecond)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ReferenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ReferenceProof
