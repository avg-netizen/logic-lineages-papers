module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
/-- Native counterpart on original natural-list encoding. -/
def NativeSuffix : Prop := ∀ (left right : List Nat),
 evaluate HistoryLookup.drop
  (evaluate HistoryLengthOffset.lengthProgram (Encodable.encode left ::ᵥ nil) ::ᵥ
   evaluate HistoryAppend.append (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) ::ᵥ nil) =
 Encodable.encode right
/-- Genuine internal suffix occurrence for arbitrary symbolic codes, without
validity/canonical-image or externally supplied extraction hypotheses. -/
def InternalSuffix : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (left right : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.DropEquationsProof.dropCall I.dropTag
   (HistoryLengthOffset.lengthCall I.lengthTag left)
   (HistoryAppend.appendCall I.appendTag left right)) right))
/-- Explicit bounded occurrence: a successful INTERNAL test of the actual right
suffix implies actual search success by one plus the true whole-stream length.
Concrete original-schema reconstruction and test success remain separate duties. -/
def InternalCoverage : Prop := ∀ n (p : Program n) (test : Program 2)
 (I : Installation p test), ∀ ctx (left right line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (RawSuffixSearch.testCall I.testTag right line) (.succ .zero))
   (.equal (RawSuffixSearch.searchCall I.searchTag
    (.succ (HistoryLengthOffset.lengthCall I.lengthTag (HistoryAppend.appendCall I.appendTag left right)))
    (HistoryAppend.appendCall I.appendTag left right) line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Targets
