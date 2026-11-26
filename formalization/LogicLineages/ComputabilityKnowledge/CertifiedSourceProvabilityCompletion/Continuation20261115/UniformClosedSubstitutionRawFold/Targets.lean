module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- Actual arbitrary symbolic count, not numeral induction. Must be obtained by
internal PA induction with both changing state and replacement carried correctly. -/
def InternalFirstTick : Prop := ∀ n (p : Program n) (itag : Nat),
 (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩ →
 ∀ ctx (count state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionFold.iterateCall itag (.succ count) state raw)
   (UniformClosedSubstitutionFold.iterateCall itag count
    (GorbowPRDefiningEquations.call (UniformClosedSubstitutionFold.IterationProof.tickTag itag) (state ::ᵥ raw ::ᵥ nil)) raw)))
/-- Literal raw-list recursion equations, valid for arbitrary encoded tail terms,
with no native-list image, successful scan, or assumed exhaustion premise. -/
def InternalRawRecursion : Prop := ∀ n (p : Program n) (ftag ptag ctag stag etag atag : Nat),
 (nodes p)[ftag]? = some ⟨3,foldCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (token tokens state out raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag .zero (HistoryKernel.pairCall ptag state out) raw)
   (HistoryKernel.pairCall ptag state out))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out) raw)
   (foldCall ftag tokens
    (HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
     (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))) raw)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Targets
