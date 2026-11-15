module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.FirstStepProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConsRunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport

/-- Consume the first actual line at an arbitrary residual count. No native
calibration or successful-history assumption is used. -/
theorem someCons {n ctx : Nat} (p : Program n) (itag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (count history line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (.succ count) (.succ history) (HistoryLookup.consCall ctag line rest) index fuel)
        (run itag ptag count
          (HistoryKernel.TransitionEquationsProof.optionValue (itag+stepTag iterationBase+1) v l a x index fuel history line)
          rest index fuel))) := by
  let kt := itag+stepTag iterationBase+1
  obtain ⟨he⟩ := FirstStepProof.firstStep p itag (HistoryKernel.kernel v l a x) hi count
    (state ptag (.succ history) (HistoryLookup.consCall ctag line rest)) index fuel
  obtain ⟨hk⟩ := FirstStepProof.someKernel p kt ptag ctag v l a x
    (IdleProof.kernelInstalled p itag v l a x hi) hp hc history line rest index fuel
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base he)
    (StationaryProof.iterationState itag count _ _ index fuel (.base hk)))⟩

theorem noneCons {n ctx : Nat} (p : Program n) (itag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (count line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (.succ count) .zero (HistoryLookup.consCall ctag line rest) index fuel)
        (run itag ptag count .zero rest index fuel))) := by
  let kt := itag+stepTag iterationBase+1
  obtain ⟨he⟩ := FirstStepProof.firstStep p itag (HistoryKernel.kernel v l a x) hi count
    (state ptag .zero (HistoryLookup.consCall ctag line rest)) index fuel
  obtain ⟨hk⟩ := HistoryIteratorSuffix.StateEquationsProof.kernelNoneCons p kt ptag ctag v l a x
    (IdleProof.kernelInstalled p itag v l a x hi) hp hc line rest index fuel
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base he)
    (StationaryProof.iterationState itag count _ _ index fuel (.base hk)))⟩

theorem nilLength {n ctx : Nat} (p : Program n) (itag ltag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
    (option rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (HistoryLengthOffset.lengthCall ltag .zero) option rest index fuel)
        (state ptag option rest))) := by
  obtain ⟨hlen⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
  obtain ⟨hz⟩ := SixSol20261113.HistoryMachine.Equations.zero p itag (HistoryKernel.kernel v l a x) hi (state ptag option rest) index fuel
  exact ⟨Hilbert.Local.finish (localTrans _ _ _
    (StationaryProof.iterationCount itag _ .zero (state ptag option rest) index fuel (.base hlen)) (.base hz))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConsRunProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConsRunProof
