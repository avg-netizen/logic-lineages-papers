module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.TrailingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice LiteralRawMP HistoryLengthOffset HistoryKernel.TransitionEquationsProof

theorem internalTrailingStep : Targets.InternalTrailingStep := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
  let V := newLineValid tag ltag ptag v l a x context psi ant
  let G := [V,H]
  let history := joinedHistory atag ptag ctag context phi psi tailI tailA
  let line := trailingLine ltag ptag context psi ant
  let kt := itag+stepTag iterationBase+1
  have hk := IdleProof.kernelInstalled p itag v l a x hi
  obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt v l a x hk
  obtain ⟨hdone⟩ := LiteralRawMP.DispatcherProof.internalDispatcher v l a x n p itag ltag atag ptag ctag dtag droptag rtag hi hl ha hp hc hd hdrop hr tag ht ctx context phi psi imp ant tailI tailA index fuel
  have hH : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
  have hV : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
  have hcheck := Hilbert.Local.mp (.mp (.base hdone) hH) hV
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
    (dispatcherTag kt v l a x) tag 4 (HistoryDispatcher.lineDispatcher v l a x)
    hdisp ht ctx (index ::ᵥ fuel ::ᵥ history ::ᵥ line ::ᵥ nil)
  obtain ⟨haccepted⟩ := HistoryKernel.OptionProof.optionAccepted p kt v l a x hk index fuel history line
  have hoption := Hilbert.Local.mp (.base haccepted) (localTrans _ _ _ (.base hcopy) hcheck)
  obtain ⟨hnew⟩ := EntryProof.newHistoryExact p (someTag kt v l a x) ptag ctag
    (someInstalled p kt v l a x hk) hp hc history context psi (lengthCall ltag ant)
  have hoption' := localTrans _ _ _ hoption (localUnary (.succ (.var 0)) _ _ (.base hnew))
  obtain ⟨hstep⟩ := ConsRunProof.someCons p itag ptag ctag v l a x hi hp hc
    (.zero : Term ctx) history line .zero index fuel
  obtain ⟨hz⟩ := SixSol20261113.HistoryMachine.Equations.zero p itag (HistoryKernel.kernel v l a x) hi
    (state ptag (optionValue kt v l a x index fuel history line) .zero) index fuel
  have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ (.zero : Term ctx) _ .zero
    hoption' (.base (.logical (.reflexive .zero)))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hz) hpair))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.TrailingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.TrailingProof
