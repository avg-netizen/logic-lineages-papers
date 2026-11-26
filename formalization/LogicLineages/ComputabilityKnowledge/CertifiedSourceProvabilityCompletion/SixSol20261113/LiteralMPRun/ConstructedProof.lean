module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.TrailingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.ConstructedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice LiteralRawMP

theorem internalConstructedRun : Targets.InternalConstructedRun := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag hm ctx context phi psi imp ant tailI tailA index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
  let V := newLineValid tag ltag ptag v l a x context psi ant
  let G := [V,H]
  let prefixCode := HistoryAppend.appendCall atag imp ant
  let suffix := trailingLines ltag ptag ctag context psi ant
  let code := HistoryAppend.appendCall atag prefixCode suffix
  let history := joinedHistory atag ptag ctag context phi psi tailI tailA
  have hH : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
  have hV : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
  have hI := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hH
  have hA := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hH
  obtain ⟨hjoin⟩ := AppendRunsProof.internalAppendRuns v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx imp ant
    (implicationHistory atag ptag ctag context phi psi tailI) (antecedentHistory ptag ctag context phi tailA) index fuel
  have hj := Hilbert.Local.mp (.mp (.base hjoin) hI) hA
  obtain ⟨hpre⟩ := PrefixProof.internalPrefixSplice v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx prefixCode suffix .zero history index fuel
  have hprefix := Hilbert.Local.mp (.base hpre) hj
  obtain ⟨htrail⟩ := TrailingProof.internalTrailingStep v l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
  have hlast := Hilbert.Local.mp (.mp (.base htrail) hH) hV
  obtain ⟨hf⟩ := ConversionProof.fusionAt p itag (HistoryKernel.kernel v l a x) hi
    (lengthCall ltag prefixCode) (.succ .zero) (state ptag (.succ .zero) code) index fuel
  have hmid := StationaryProof.iterationState itag (.succ .zero) _ _ index fuel hprefix
  have hsum := localTrans _ _ _ (.base hf) (localTrans _ _ _ hmid hlast)
  obtain ⟨hdata⟩ := LengthDataProof.lengthData n p ltag atag droptag ctag hl ha hdrop hc ctx prefixCode suffix .zero
  have hlen : Derivation T (.equal (lengthCall ltag code) (.add (lengthCall ltag prefixCode) (lengthCall ltag suffix))) :=
    .mp (.logical (.andRight _ _)) (.mp (.logical (.andRight _ _)) hdata)
  obtain ⟨hcns⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx (trailingLine ltag ptag context psi ant) (.zero : Term ctx)
  obtain ⟨hnil⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
  have hsingle : Hilbert.Local T ctx G (.equal (lengthCall ltag suffix) (.succ .zero)) :=
    localTrans _ _ _ (.base hcns) (localUnary (.succ (.var 0)) _ _ (.base hnil))
  have hadd := localUnary (.add (liftTerm (lengthCall ltag prefixCode)) (.var 0)) _ _ hsingle
  have hadd' : Hilbert.Local T ctx G
      (.equal (.add (lengthCall ltag prefixCode) (lengthCall ltag suffix))
        (.add (lengthCall ltag prefixCode) (.succ .zero))) := by
    simpa only [GorbowSubstitution.substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hadd
  have htotal := localTrans _ _ _ (.base hlen) hadd' 
  have hcount := StationaryProof.iterationCount itag _ _ (state ptag (.succ .zero) code) index fuel htotal
  obtain ⟨hcv⟩ := ConversionProof.internalBoundConversion v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx code (.succ .zero) index fuel
  have hcode := localTrans _ _ _ (.base hcv) (localTrans _ _ _ hcount hsum)
  obtain ⟨hconstructor⟩ := ConstructorProof.internalConstructor n p mtag ltag atag ptag ctag hm hl ha hp hc ctx context psi imp ant
  have hcount' := StationaryProof.iterationCount (T := T) (G := G) itag _ code
    (state ptag (.succ .zero) (certificate mtag context psi imp ant)) index fuel (.base hconstructor)
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) ptag (.succ (.zero : Term ctx)) _ (.succ .zero) code
    (.base (.logical (.reflexive (.succ .zero)))) (.base hconstructor)
  have hstate := StationaryProof.iterationState itag code _ _ index fuel hs
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (localTrans _ _ _ hcount' (localTrans _ _ _ hstate hcode))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.ConstructedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.ConstructedProof
