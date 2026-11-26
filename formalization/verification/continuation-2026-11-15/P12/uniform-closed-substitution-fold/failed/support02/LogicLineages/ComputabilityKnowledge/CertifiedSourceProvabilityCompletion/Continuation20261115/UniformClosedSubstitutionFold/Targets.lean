module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- All original states/outputs and token lists, not only successful scans. -/
def ExactOriginalFold : Prop := ∀ (s : GorbowSubstitutionCode.OutputState) (tokens raw : List Nat),
 GorbowSyntaxValidation.validTerm 0 raw = true →
 evaluate iterator (tokens.length ::ᵥ Nat.pair (Encodable.encode tokens) (Encodable.encode s) ::ᵥ
  Encodable.encode raw ::ᵥ nil) =
 Nat.pair 0 (Encodable.encode (tokens.foldl (GorbowSubstitutionCode.subStep 1 0 [raw]) s))
/-- Actual defining-equation composition, on arbitrary symbolic inputs. -/
def InternalSubStep : Prop := ∀ n (p : Program n) (qtag ptag stag etag atag : Nat),
 (nodes p)[qtag]? = some ⟨3,subStepCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (state out token raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (subStepCall qtag (HistoryKernel.pairCall ptag state out) token raw)
   (HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
    (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw)))))
/-- Finite constructor-built token lists only; elements and state/output/replacement
are arbitrary terms. This is not arbitrary encoded-list exhaustion or reflection. -/
def InternalFiniteFold : Prop := ∀ n (p : Program n) (itag ptag ctag stag etag atag : Nat),
 (nodes p)[itag]? = some ⟨3,iterator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (tokens : List (Term ctx)) (state out raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iterateCall itag (Term.numeral tokens.length)
   (HistoryKernel.pairCall ptag (tokenTerms ctag tokens) (HistoryKernel.pairCall ptag state out)) raw)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (foldTerms stag etag atag raw tokens state out).1
      (foldTerms stag etag atag raw tokens state out).2))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Targets
