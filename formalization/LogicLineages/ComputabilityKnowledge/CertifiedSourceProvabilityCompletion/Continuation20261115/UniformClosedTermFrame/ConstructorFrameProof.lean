module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorFrameProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorStepTargets
noncomputable def packedCongruence {T : Sentence → Prop} {ctx : Nat} (ptag : Nat)
 (a b out : Term ctx) (h : Derivation T (.equal a b)) :
 Derivation T (.equal (HistoryKernel.pairCall ptag (.succ a) out) (HistoryKernel.pairCall ptag (.succ b) out)) := by
 have hs := localUnary (.succ (.var 0)) a b (Hilbert.Local.base (Gamma := []) h)
 have hs' : Hilbert.Local T ctx [] (.equal (.succ a) (.succ b)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hs
 exact (HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := []) ptag
  (.succ a) out (.succ b) out hs' (.base (.logical (.reflexive out)))).finish
/-- One actual constructor transition commutes with a pending-prefix frame.
The raw rest is not assumed to be a list image or a valid task stack. -/
theorem consumes {n ctx : Nat} (p : Program n) (ftag ptag ctag stepTag etag atag xtag l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound pending rest tokens out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionRawFold.foldCall ftag
   (HistoryLookup.consCall ctag (Term.numeral (token ctor)) tokens)
   (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag
    (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) bound) pending) rest)) out) raw)
   (UniformClosedSubstitutionRawFold.foldCall ftag tokens
    (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag
     (output ptag ctag atag ctor bound pending) rest))
     (HistoryAppend.appendCall atag out (HistoryLookup.consCall ctag (Term.numeral (token ctor)) .zero))) raw))) := by
 let task := LiteralSyntaxStep.taskCall ptag (kind ctor) bound
 let framed := HistoryAppend.appendCall atag pending rest
 let chunk := HistoryLookup.consCall ctag (Term.numeral (n := ctx) (token ctor)) .zero
 let out' := HistoryAppend.appendCall atag out chunk
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx task pending rest
 have hstate := packedCongruence ptag _ _ out hcons
 have hinput := UniformFixedFormulaAgreement.FoldProof.stateCongruence ftag
  (HistoryLookup.consCall ctag (Term.numeral (token ctor)) tokens) _ _ raw hstate
 obtain ⟨hconsume⟩ := UniformFixedFormulaAgreement.ConstructorProof.consume p ftag ptag ctag stepTag etag atag xtag
  hf hp hc hs he ha hx ctor hmarker bound framed tokens out raw
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity n p atag ctag l r ha hc hl hr ctx
  (FinitePrefixTargets.prefixTerm ctag (tasks ptag bound ctor)) pending rest
 have hfinal := packedCongruence ptag _ _ out' (Support.equalitySymmetry _ _ hassoc)
 have htail := UniformFixedFormulaAgreement.FoldProof.stateCongruence ftag tokens _ _ raw hfinal
 exact ⟨Logic.trans _ _ _ hinput (Logic.trans _ _ _ hconsume htail)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorFrameProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorFrameProof
