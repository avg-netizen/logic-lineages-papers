module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.AtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.TransformProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
/-- A term, not a newly assumed registered packedFrame program. This is the
simulation map used by raw-fold framing when only outputFrame is installed. -/
def transformed {ctx : Nat} (ptag ftag ltag rtag : Nat) (prefixCode packed : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (call ltag (packed ::ᵥ nil))
  (frameCall ftag prefixCode (call rtag (packed ::ᵥ nil)))
theorem substTransformed {m n : Nat} (s : Fin m → Term n) ptag ftag ltag rtag (prefixCode packed : Term m) :
 substitute s (transformed ptag ftag ltag rtag prefixCode packed) =
 transformed ptag ftag ltag rtag (substitute s prefixCode) (substitute s packed) := by
 simp only [transformed,HistoryKernel.pairCall,frameCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
noncomputable def frameCongruence {ctx : Nat} {T : Sentence → Prop} ftag (prefixCode a b : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (frameCall ftag prefixCode a) (frameCall ftag prefixCode b)) := by
 apply Hilbert.Local.finish
 apply callCongruence (T := T) (G := []) ftag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact .base (.logical (.reflexive prefixCode))
 | succ i => cases i using Fin.cases with
   | zero => exact .base h
   | succ i => exact Fin.elim0 i
theorem atPair {n ctx : Nat} (p : Program n) (ptag ftag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode tokens acc : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transformed ptag ftag ltag rtag prefixCode (HistoryKernel.pairCall ptag tokens acc))
   (HistoryKernel.pairCall ptag tokens (frameCall ftag prefixCode acc)))) := by
 obtain ⟨hleft⟩ := HistoryLookup.DestructorProof.decoderCrossPair p ltag ptag false hl hp tokens acc
 obtain ⟨hright⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp tokens acc
 have hframe := frameCongruence ftag prefixCode _ acc hright
 exact ⟨(HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag _ _ tokens (frameCall ftag prefixCode acc) (.base hleft) (.base hframe)).finish⟩
theorem atNested {n ctx : Nat} (p : Program n) (ptag ftag atag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,outputFrame⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode tokens state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transformed ptag ftag ltag rtag prefixCode
    (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)))
   (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out))))) := by
 obtain ⟨hpair⟩ := atPair p ptag ftag ltag rtag hp hl hr prefixCode tokens (HistoryKernel.pairCall ptag state out)
 obtain ⟨hframe⟩ := AtomsProof.outputEquation p ftag ptag atag hf hp ha prefixCode state out
 have hcong := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag tokens _ tokens _ (.base (.logical (.reflexive tokens))) (.base hframe)
 exact ⟨Logic.trans _ _ _ hpair hcong.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.TransformProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.TransformProof
