module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.FirstProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.BindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.DispatcherSupportProof
open UniformClosedSubstitutionFold (iterateCall)
noncomputable def countCongruence {ctx : Nat} {T : Sentence → Prop} tag (a b state raw : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (iterateCall tag a state raw) (iterateCall tag b state raw)) := by
 apply Hilbert.Local.finish
 apply callCongruence (T := T) (G := []) tag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact .base h
 | succ i => cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive state))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i
theorem nilFold {n ctx : Nat} (p : Program n) (ftag ptag itag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag .zero state raw) state)) := by
 obtain ⟨hb⟩ := BindingProof.binding p ftag ptag itag ltag rtag hf hp hi hl hr .zero state raw
 obtain ⟨hl0⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
 obtain ⟨hz⟩ := UniformClosedSubstitutionFold.IterationProof.zero p itag hi (HistoryKernel.pairCall ptag .zero state) raw
 have hc := countCongruence itag _ .zero (HistoryKernel.pairCall ptag .zero state) raw hl0
 have hm := HistoryLookup.DestructorProof.unaryCallCongruence rtag _ _ (Logic.trans _ _ _ hc hz)
 obtain ⟨hd⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp .zero state
 exact ⟨Logic.trans _ _ _ hb (Logic.trans _ _ _ hm hd)⟩
theorem consFold {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag itag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token tokens state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out) raw)
   (foldCall ftag tokens
    (HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
     (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))) raw))) := by
 let old := HistoryKernel.pairCall ptag state out
 let row := HistoryLookup.consCall ctag token tokens
 let packed := HistoryKernel.pairCall ptag row old
 let next := HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
  (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))
 obtain ⟨hb⟩ := BindingProof.binding p ftag ptag itag ltag rtag hf hp hi hl hr row old raw
 obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx token tokens
 have hcount := countCongruence itag _ _ packed raw hlen
 obtain ⟨hfirst⟩ := FirstProof.internalFirst n p itag hi ctx (HistoryLengthOffset.lengthCall ltag tokens) packed raw
 obtain ⟨htick⟩ := UniformClosedSubstitutionFold.TickProof.tickCons p ptag ctag stag etag atag hp hc hs he ha
  token tokens state out raw (UniformClosedSubstitutionFold.IterationProof.tickTag itag)
  (UniformClosedSubstitutionFold.IterationProof.tickInstalled p itag hi)
 have hrun := UniformClosedSubstitutionFold.Proof.runCongruence itag
  (HistoryLengthOffset.lengthCall ltag tokens) _ _ raw htick.finish
 have hproject := HistoryLookup.DestructorProof.unaryCallCongruence rtag _ _
  (Logic.trans _ _ _ hcount (Logic.trans _ _ _ hfirst hrun))
 obtain ⟨hnew⟩ := BindingProof.binding p ftag ptag itag ltag rtag hf hp hi hl hr tokens next raw
 exact ⟨Logic.trans _ _ _ hb (Logic.trans _ _ _ hproject (Support.equalitySymmetry _ _ hnew))⟩
theorem exactRawRecursion : Targets.InternalRawRecursion := by
 intro n p ftag ptag ctag stag etag atag hf hp hc hs he ha ctx token tokens state out raw
 obtain ⟨hr,hi,hl⟩ := InstallationProof.installed p ftag hf
 exact ⟨nilFold p ftag ptag _ _ _ hf hp hi hl hr (HistoryKernel.pairCall ptag state out) raw,
  consFold p ftag ptag ctag stag etag atag _ _ _ hf hp hc hs he ha hi hl hr token tokens state out raw⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Proof
