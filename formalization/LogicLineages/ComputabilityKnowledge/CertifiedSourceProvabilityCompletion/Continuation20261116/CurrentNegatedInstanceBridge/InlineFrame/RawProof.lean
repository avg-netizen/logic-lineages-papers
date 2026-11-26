module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.IterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.RawProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph TransformProof
open HistoryLookup.DestructorProof (unaryCallCongruence)
theorem rawFrame {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p)
 (tokens prefixCode state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionRawFold.foldCall I.ftag tokens
   (frameTerm I.ptag I.atag I.ltag I.rtag prefixCode state) raw)
   (frameTerm I.ptag I.atag I.ltag I.rtag prefixCode
    (UniformClosedSubstitutionRawFold.foldCall I.ftag tokens state raw)))) := by
 obtain ⟨_,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p I.ftag I.h_ftag
 let itag := UniformClosedSubstitutionRawFold.InstallationProof.iteratorTag I.ftag
 let lentag := UniformClosedSubstitutionRawFold.InstallationProof.lengthTag I.ftag
 let count := HistoryLengthOffset.lengthCall lentag tokens
 let initial := HistoryKernel.pairCall I.ptag tokens state
 obtain ⟨hleft⟩ := UniformClosedSubstitutionRawFold.BindingProof.binding p I.ftag I.ptag itag lentag I.rtag
  I.h_ftag I.h_ptag hi hlen I.h_rtag tokens (frameTerm I.ptag I.atag I.ltag I.rtag prefixCode state) raw
 obtain ⟨hinit⟩ := TransformProof.atPair p I.ptag I.atag I.ltag I.rtag I.h_ptag I.h_ltag I.h_rtag prefixCode tokens state
 have hinitRun := UniformClosedSubstitutionFold.Proof.runCongruence itag count _ _ raw (Support.equalitySymmetry _ _ hinit)
 obtain ⟨hsim⟩ := IterationProof.arbitraryCount p I.ptag I.atag I.ltag I.rtag itag I.ctag I.stepTag I.etag I.htag I.ttag
  I.h_ptag I.h_atag I.h_ltag I.h_rtag hi I.h_ctag I.h_stepTag I.h_etag I.h_htag I.h_ttag count prefixCode initial raw
 have hproject := unaryCallCongruence I.rtag _ _ (Logic.trans _ _ _ hinitRun hsim)
 obtain ⟨hfinish⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.rtag I.ptag true I.h_rtag I.h_ptag
  (call I.ltag (UniformClosedSubstitutionFold.iterateCall itag count initial raw ::ᵥ nil))
  (frameTerm I.ptag I.atag I.ltag I.rtag prefixCode
   (call I.rtag (UniformClosedSubstitutionFold.iterateCall itag count initial raw ::ᵥ nil)))
 obtain ⟨hright⟩ := UniformClosedSubstitutionRawFold.BindingProof.binding p I.ftag I.ptag itag lentag I.rtag
  I.h_ftag I.h_ptag hi hlen I.h_rtag tokens state raw
 have hend := TransformProof.frameCongruence I.ptag I.atag I.ltag I.rtag prefixCode _ _ (Support.equalitySymmetry _ _ hright)
 exact ⟨Logic.trans _ _ _ hleft (Logic.trans _ _ _ hproject (Logic.trans _ _ _ hfinish hend))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.RawProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.RawProof
