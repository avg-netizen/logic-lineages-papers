module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TransformProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
/-- Inline simulation map using only actual pair/append/decoder nodes.
Neither outputFrame nor packedFrame membership is assumed. -/
def transformed {ctx : Nat} (ptag atag ltag rtag : Nat) (prefixCode packed : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (call ltag (packed ::ᵥ nil))
  (frameTerm ptag atag ltag rtag prefixCode (call rtag (packed ::ᵥ nil)))
theorem substTransformed {m n : Nat} (s : Fin m → Term n) ptag atag ltag rtag (prefixCode packed : Term m) :
 substitute s (transformed ptag atag ltag rtag prefixCode packed) =
 transformed ptag atag ltag rtag (substitute s prefixCode) (substitute s packed) := by
 simp only [transformed,HistoryKernel.pairCall,AtomsProof.substFrame,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
noncomputable def frameCongruence {ctx : Nat} {T : Sentence → Prop} ptag atag ltag rtag (prefixCode a b : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (frameTerm ptag atag ltag rtag prefixCode a) (frameTerm ptag atag ltag rtag prefixCode b)) := by
 have d := Logic.unary (frameTerm ptag atag ltag rtag (liftTerm prefixCode) (.var 0)) a b h
 simpa only [AtomsProof.substFrame,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using d
theorem atPair {n ctx : Nat} (p : Program n) (ptag atag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode tokens acc : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transformed ptag atag ltag rtag prefixCode (HistoryKernel.pairCall ptag tokens acc))
   (HistoryKernel.pairCall ptag tokens (frameTerm ptag atag ltag rtag prefixCode acc)))) := by
 obtain ⟨hleft⟩ := HistoryLookup.DestructorProof.decoderCrossPair p ltag ptag false hl hp tokens acc
 obtain ⟨hright⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp tokens acc
 have hframe := frameCongruence ptag atag ltag rtag prefixCode _ acc hright
 exact ⟨(HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag _ _ tokens (frameTerm ptag atag ltag rtag prefixCode acc) (.base hleft) (.base hframe)).finish⟩
theorem atNested {n ctx : Nat} (p : Program n) (ptag atag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode tokens state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transformed ptag atag ltag rtag prefixCode
    (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)))
   (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out))))) := by
 obtain ⟨hpair⟩ := atPair p ptag atag ltag rtag hp hl hr prefixCode tokens (HistoryKernel.pairCall ptag state out)
 obtain ⟨hframe⟩ := AtomsProof.outputEquation p ptag atag ltag rtag hp hl hr prefixCode state out
 have hcong := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag tokens _ tokens _ (.base (.logical (.reflexive tokens))) (.base hframe)
 exact ⟨Logic.trans _ _ _ hpair hcong.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TransformProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TransformProof
