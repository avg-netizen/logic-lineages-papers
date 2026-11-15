module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.IterationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.BindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph TransformProof
open HistoryLookup.DestructorProof (unaryCallCongruence)
theorem exactTick : Targets.InternalTickFrame := by
 intro n p qtag ttag hq ht ctx prefixCode state raw
 obtain ⟨ftag,hf⟩ := BindingProof.outputInstalled p qtag hq
 obtain ⟨ptag,ctag,stag,etag,atag,htag,tailtag,ltag,rtag,hp,hc,hs,he,ha,hh,htail,hl,hr⟩ := InstallationProof.auxiliaries p ftag ttag hf ht
 obtain ⟨hb⟩ := BindingProof.packedBinding p qtag ptag ftag ltag rtag hq hp hf hl hr prefixCode state
 obtain ⟨hcommute⟩ := AllStateProof.arbitraryState p ptag ftag atag ltag rtag ttag ctag stag etag htag tailtag
  hp hf ha hl hr ht hc hs he hh htail prefixCode state raw
 obtain ⟨hend⟩ := BindingProof.packedBinding p qtag ptag ftag ltag rtag hq hp hf hl hr prefixCode
  (UniformSubstitutionErasure.newTickCall ttag state raw)
 have hstart := UniformClosedSubstitutionFold.IterationProof.tickCongruence ttag _ _ raw hb
 exact ⟨Logic.trans _ _ _ hstart (Logic.trans _ _ _ hcommute (Support.equalitySymmetry _ _ hend))⟩
theorem exactIterator : Targets.InternalIteratorFrame := by
 intro n p qtag itag hq hi ctx count prefixCode state raw
 obtain ⟨ftag,hf⟩ := BindingProof.outputInstalled p qtag hq
 let ttag := UniformClosedSubstitutionFold.IterationProof.tickTag itag
 have ht := UniformClosedSubstitutionFold.IterationProof.tickInstalled p itag hi
 obtain ⟨ptag,ctag,stag,etag,atag,htag,tailtag,ltag,rtag,hp,hc,hs,he,ha,hh,htail,hl,hr⟩ := InstallationProof.auxiliaries p ftag ttag hf ht
 obtain ⟨hb⟩ := BindingProof.packedBinding p qtag ptag ftag ltag rtag hq hp hf hl hr prefixCode state
 obtain ⟨hcommute⟩ := IterationProof.arbitraryCount p ptag ftag atag ltag rtag itag ctag stag etag htag tailtag
  hp hf ha hl hr hi hc hs he hh htail count prefixCode state raw
 obtain ⟨hend⟩ := BindingProof.packedBinding p qtag ptag ftag ltag rtag hq hp hf hl hr prefixCode
  (UniformClosedSubstitutionFold.iterateCall itag count state raw)
 have hstart := UniformClosedSubstitutionFold.Proof.runCongruence itag count _ _ raw hb
 exact ⟨Logic.trans _ _ _ hstart (Logic.trans _ _ _ hcommute (Support.equalitySymmetry _ _ hend))⟩
/-- No packedFrame tag is selected or assumed in this proof. -/
theorem exactRawFold : Targets.InternalRawFoldFrame := by
 intro n p ftag qtag hf hq ctx tokens prefixCode state raw
 obtain ⟨_,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p qtag hq
 let itag := UniformClosedSubstitutionRawFold.InstallationProof.iteratorTag qtag
 let lentag := UniformClosedSubstitutionRawFold.InstallationProof.lengthTag qtag
 let ttag := UniformClosedSubstitutionFold.IterationProof.tickTag itag
 have ht := UniformClosedSubstitutionFold.IterationProof.tickInstalled p itag hi
 obtain ⟨ptag,ctag,stag,etag,atag,htag,tailtag,ltag,rtag,hp,hc,hs,he,ha,hh,htail,hl,hr⟩ := InstallationProof.auxiliaries p ftag ttag hf ht
 let count := HistoryLengthOffset.lengthCall lentag tokens
 let initial := HistoryKernel.pairCall ptag tokens state
 obtain ⟨hleft⟩ := UniformClosedSubstitutionRawFold.BindingProof.binding p qtag ptag itag lentag rtag
  hq hp hi hlen hr tokens (frameCall ftag prefixCode state) raw
 obtain ⟨hinit⟩ := TransformProof.atPair p ptag ftag ltag rtag hp hl hr prefixCode tokens state
 have hinitRun := UniformClosedSubstitutionFold.Proof.runCongruence itag count _ _ raw (Support.equalitySymmetry _ _ hinit)
 obtain ⟨hsim⟩ := IterationProof.arbitraryCount p ptag ftag atag ltag rtag itag ctag stag etag htag tailtag
  hp hf ha hl hr hi hc hs he hh htail count prefixCode initial raw
 have hproject := unaryCallCongruence rtag _ _ (Logic.trans _ _ _ hinitRun hsim)
 obtain ⟨hfinish⟩ := BindingProof.projectTransform p ptag ftag ltag rtag hp hr prefixCode
  (UniformClosedSubstitutionFold.iterateCall itag count initial raw)
 obtain ⟨hright⟩ := UniformClosedSubstitutionRawFold.BindingProof.binding p qtag ptag itag lentag rtag
  hq hp hi hlen hr tokens state raw
 have hend := TransformProof.frameCongruence ftag prefixCode _ _ (Support.equalitySymmetry _ _ hright)
 exact ⟨Logic.trans _ _ _ hleft (Logic.trans _ _ _ hproject (Logic.trans _ _ _ hfinish hend))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Proof
