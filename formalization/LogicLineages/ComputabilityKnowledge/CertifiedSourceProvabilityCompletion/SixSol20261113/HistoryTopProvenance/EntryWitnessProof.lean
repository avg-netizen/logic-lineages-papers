module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryWitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.EntryProof HistoryKernel.TransitionEquationsProof

/-- Actual accepted dispatcher plus the actual entry value identifies a consumed
line with the target context/raw fields. Validity is only nonzero. -/
theorem fromAcceptedEntry {n ctx : Nat} (p : Program n) (itag etag ptag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (he : (nodes p)[etag]? = some ⟨3,HistoryKernel.entry⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (index fuel history line context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.imp (.equal (HistoryDispatcher.dispatcherCall (dispatcherTag (kernelTag itag) v l a x)
     index fuel history line) (.succ .zero))
    (.imp (.equal (entryValue etag line) (HistoryKernel.pairCall ptag context raw))
      (topWitness (validityTag itag v l a x) leftTag rightTag context raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let D := Formula.equal (HistoryDispatcher.dispatcherCall (dispatcherTag (kernelTag itag) v l a x)
     index fuel history line) (.succ .zero)
 let E := Formula.equal (entryValue etag line) (HistoryKernel.pairCall ptag context raw)
 let lc := call leftTag (line ::ᵥ nil)
 let lr := call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil)
 obtain ⟨hn⟩ := EntryProof.entryValueNormalized p etag ptag leftTag rightTag he hp hl hr line
 obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx lc lr context raw
 obtain ⟨hv⟩ := ValidityProof.dispatcherNonzero p itag v l a x hi index fuel history line
 have hd : Hilbert.Local T ctx [E,D] D := .hypothesis (by simp)
 have heq : Hilbert.Local T ctx [E,D] E := .hypothesis List.mem_cons_self
 have pairEq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hn)) heq
 have fields := Hilbert.Local.mp (.base hinj) pairEq
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) fields
 have hr := Hilbert.Local.mp (.base (.logical (.andRight _ _))) fields
 have valid := Hilbert.Local.mp (.base hv) hd
 have lf : Hilbert.Local T ctx [E,D]
   (lineFields (validityTag itag v l a x) leftTag rightTag line context raw) :=
   .mp (.mp (.base (.logical (.andIntro _ _))) hc)
     (.mp (.mp (.base (.logical (.andIntro _ _))) hr) valid)
 have result := Hilbert.Local.mp
   (.base (SyntaxProof.witnessIntro (validityTag itag v l a x) leftTag rightTag line context raw)) lf
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge result))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryWitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryWitnessProof
