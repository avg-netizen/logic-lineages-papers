module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual machine commuting square on every packed code, including empty
remaining input and failed/malformed syntax states. No native-image premise. -/
def InternalTickFrame : Prop := ∀ n (p : Program n) (ftag ttag : Nat),
 (nodes p)[ftag]? = some ⟨2,packedFrame⟩ →
 (nodes p)[ttag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩ →
 ∀ ctx (prefixCode state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformSubstitutionErasure.newTickCall ttag (frameCall ftag prefixCode state) raw)
   (frameCall ftag prefixCode (UniformSubstitutionErasure.newTickCall ttag state raw))))
/-- Genuine internal arbitrary-count simulation, not a native/numeral fold. -/
def InternalIteratorFrame : Prop := ∀ n (p : Program n) (ftag itag : Nat),
 (nodes p)[ftag]? = some ⟨2,packedFrame⟩ →
 (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩ →
 ∀ ctx (count prefixCode state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionFold.iterateCall itag count (frameCall ftag prefixCode state) raw)
   (frameCall ftag prefixCode (UniformClosedSubstitutionFold.iterateCall itag count state raw))))
/-- Actual length-driven fold, arbitrary encoded token list and OutputState.
No length=image or successful scan hypothesis; helper tags must be recovered. -/
def InternalRawFoldFrame : Prop := ∀ n (p : Program n) (ftag qtag : Nat),
 (nodes p)[ftag]? = some ⟨2,outputFrame⟩ →
 (nodes p)[qtag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ →
 ∀ ctx (tokens prefixCode state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionRawFold.foldCall qtag tokens (frameCall ftag prefixCode state) raw)
   (frameCall ftag prefixCode (UniformClosedSubstitutionRawFold.foldCall qtag tokens state raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Targets
