module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConversionProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.FirstStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem firstStep {n ctx : Nat} (p : Program n) itag (k : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator k⟩) (count code index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (iterationCall itag (.succ count) code index fuel)
        (iterationCall itag count (call (itag+stepTag iterationBase+1) (code ::ᵥ index ::ᵥ fuel ::ᵥ nil)) index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let kt := itag+stepTag iterationBase+1
  obtain ⟨hf⟩ := ConversionProof.fusionAt p itag k hi (.succ .zero) count code index fuel
  obtain ⟨hz⟩ := SixSol20261113.HistoryMachine.Equations.zero p itag k hi code index fuel
  obtain ⟨ho⟩ := SixSol20261113.HistoryMachine.Equations.successor p itag k hi (.zero : Term ctx) code index fuel
  have hk := localUnary (call kt (.var 0 ::ᵥ liftTerm index ::ᵥ liftTerm fuel ::ᵥ nil)) _ _ (Hilbert.Local.base (Gamma := []) hz)
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hk
  have h1 := localTrans _ _ _ (.base ho) hk
  have hcount : Derivation T (.equal (.add (.succ .zero) count) (.succ count)) :=
    Logic.trans _ _ _ (successorLeft .zero count) (Hilbert.Local.finish (localUnary (.succ (.var 0)) _ _ (.base (zeroLeft count))))
  have hc := StationaryProof.iterationCount (T := T) (G := []) itag (.succ count) (.add (.succ .zero) count) code index fuel (.base (Support.equalitySymmetry _ _ hcount))
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ hc (localTrans _ _ _ (.base hf)
    (StationaryProof.iterationState itag count _ _ index fuel h1)))⟩

theorem someKernel {n ctx : Nat} (p : Program n) (ktag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hk : (nodes p)[ktag]? = some ⟨3,HistoryKernel.kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (history line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryKernel.kernelCall ktag (state ptag (.succ history) (HistoryLookup.consCall ctag line rest)) index fuel)
        (state ptag (HistoryKernel.TransitionEquationsProof.optionValue ktag v l a x index fuel history line) rest))) := by
  obtain ⟨he⟩ := HistoryKernel.NormalProof.kernelEquation p ktag ptag ctag v l a x hk hp hc index fuel history line rest
  obtain ⟨hpair,_,_,_,_⟩ := HistoryKernel.OptionProof.kernelNodes p ktag v l a x hk
  obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p
    (HistoryKernel.TransitionEquationsProof.outputPairTag ktag v l a x) ptag hpair hp
    (HistoryKernel.TransitionEquationsProof.optionValue ktag v l a x index fuel history line) rest
  exact ⟨Logic.trans _ _ _ he hcopy⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.FirstStepProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.FirstStepProof
