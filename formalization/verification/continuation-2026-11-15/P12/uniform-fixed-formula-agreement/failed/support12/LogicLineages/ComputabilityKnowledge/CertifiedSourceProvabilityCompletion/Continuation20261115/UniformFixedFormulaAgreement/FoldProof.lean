module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.AtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph UniformClosedSubstitutionRawFold
/-- Congruence of the actual fold in its packed accumulator. -/
noncomputable def stateCongruence {ctx : Nat} {T : Sentence → Prop} (tag : Nat)
 (tokens a b raw : Term ctx) (h : Derivation T (.equal a b)) :
 Derivation T (.equal (foldCall tag tokens a raw) (foldCall tag tokens b raw)) := by
 apply Logic.callCongruence T tag
 intro i
 cases i using Fin.cases with
 | zero => exact .logical (.reflexive _)
 | succ i => cases i using Fin.cases with
   | zero => exact h
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive _)
     | succ i => exact Fin.elim0 i
/-- The literal next OutputState, defined using only already installed tags. -/
def next {ctx : Nat} (ptag stag etag atag ltag rtag : Nat)
 (token state raw : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag
  (LiteralSyntaxStep.stepCall stag (call ltag (state ::ᵥ nil)) token)
  (HistoryAppend.appendCall atag (call rtag (state ::ᵥ nil))
   (UniformClosedSubstitutionEmit.emitCall etag (call ltag (state ::ᵥ nil)) token raw))
/-- Arbitrary numeric accumulator, not a supplied pair-image premise. -/
theorem consAny {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token tokens state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (HistoryLookup.consCall ctag token tokens) state raw)
   (foldCall ftag tokens (next ptag stag etag atag ltag rtag token state raw) raw))) := by
 obtain ⟨hrecon⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction
  n p ptag ltag rtag hp hl hr ctx state
 have hchange := stateCongruence ftag (HistoryLookup.consCall ctag token tokens) _ state raw hrecon
 obtain ⟨hcons⟩ := (StatementChecks.exactRawRecursion n p ftag ptag ctag stag etag atag
  hf hp hc hs he ha ctx token tokens (call ltag (state ::ᵥ nil)) (call rtag (state ::ᵥ nil)) raw).2
 exact ⟨Logic.trans _ _ _ (Support.equalitySymmetry _ _ hchange) hcons⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
