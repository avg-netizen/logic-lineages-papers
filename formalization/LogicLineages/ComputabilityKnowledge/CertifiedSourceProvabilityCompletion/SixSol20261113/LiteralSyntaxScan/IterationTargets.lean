module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open Iteration
/-- Genuine actual iterator addition, without image or success assumptions. -/
def InternalAddition : Prop := ∀ n (p : Program n) itag,
 (nodes p)[itag]? = some ⟨2,iterator⟩ → ∀ ctx (a b state : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (runCall itag (.add a b) state)
   (runCall itag b (runCall itag a state))))
/-- Universal operational prefix splice, stronger than successful scan fusion. -/
def InternalSplice : Prop := ∀ n (p : Program n) itag ltag atag ptag rtag,
 (nodes p)[itag]? = some ⟨2,iterator⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (left right state : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (splice itag ltag atag ptag rtag left right state))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.IterationTargets
