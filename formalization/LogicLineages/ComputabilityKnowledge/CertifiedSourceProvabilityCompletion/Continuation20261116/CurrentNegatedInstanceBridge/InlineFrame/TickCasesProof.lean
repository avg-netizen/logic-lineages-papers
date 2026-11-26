module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TransformProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TickCasesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport TransformProof
noncomputable def transformCongruence {ctx : Nat} {T : Sentence → Prop} ptag atag ltag rtag (prefixCode a b : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (transformed ptag atag ltag rtag prefixCode a) (transformed ptag atag ltag rtag prefixCode b)) := by
 have d := Logic.unary (transformed ptag atag ltag rtag (liftTerm prefixCode) (.var 0)) a b h
 simpa only [substTransformed,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using d
theorem nilCase {n ctx : Nat} (p : Program n) (ptag atag ltag rtag ttag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ht : (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (prefixCode state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformSubstitutionErasure.newTickCall ttag
    (transformed ptag atag ltag rtag prefixCode (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag state out))) raw)
   (transformed ptag atag ltag rtag prefixCode (UniformSubstitutionErasure.newTickCall ttag
    (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag state out)) raw)))) := by
 obtain ⟨hframe⟩ := atNested p ptag atag ltag rtag hp ha hl hr prefixCode .zero state out
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.TickProof.tickNil p ptag hp
  (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out)) raw ttag ht
 obtain ⟨hold⟩ := UniformClosedSubstitutionFold.TickProof.tickNil p ptag hp (HistoryKernel.pairCall ptag state out) raw ttag ht
 have hleft := Logic.trans _ _ _ (UniformClosedSubstitutionFold.IterationProof.tickCongruence ttag _ _ raw hframe) hnew.finish
 have hright := Logic.trans _ _ _ (transformCongruence ptag atag ltag rtag prefixCode _ _ hold.finish) hframe
 exact ⟨Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hright)⟩
theorem consCase {n ctx : Nat} (p : Program n) (ptag atag ltag rtag ttag ctag stag etag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ht : (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (prefixCode token tokens state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformSubstitutionErasure.newTickCall ttag
    (transformed ptag atag ltag rtag prefixCode
     (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out))) raw)
   (transformed ptag atag ltag rtag prefixCode (UniformSubstitutionErasure.newTickCall ttag
    (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out)) raw)))) := by
 obtain ⟨hframe⟩ := atNested p ptag atag ltag rtag hp ha hl hr prefixCode (HistoryLookup.consCall ctag token tokens) state out
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.TickProof.tickCons p ptag ctag stag etag atag hp hc hs he ha
  token tokens state (HistoryAppend.appendCall atag prefixCode out) raw ttag ht
 obtain ⟨hold⟩ := UniformClosedSubstitutionFold.TickProof.tickCons p ptag ctag stag etag atag hp hc hs he ha
  token tokens state out raw ttag ht
 obtain ⟨hnext⟩ := atNested p ptag atag ltag rtag hp ha hl hr prefixCode tokens
  (LiteralSyntaxStep.stepCall stag state token)
  (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity n p atag ctag ltag rtag ha hc hl hr ctx
  prefixCode out (UniformClosedSubstitutionEmit.emitCall etag state token raw)
 have hinner := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag (LiteralSyntaxStep.stepCall stag state token) _ (LiteralSyntaxStep.stepCall stag state token) _
  (.base (.logical (.reflexive _))) (.base hassoc)
 have houter := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag tokens _ tokens _ (.base (.logical (.reflexive tokens))) hinner
 have hleft := Logic.trans _ _ _ (UniformClosedSubstitutionFold.IterationProof.tickCongruence ttag _ _ raw hframe)
  (Logic.trans _ _ _ hnew.finish houter.finish)
 have hright := Logic.trans _ _ _ (transformCongruence ptag atag ltag rtag prefixCode _ _ hold.finish) hnext
 exact ⟨Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hright)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TickCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.TickCasesProof
