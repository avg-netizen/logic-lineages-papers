module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.AtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 HistoryRuleSuffix List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem outputAtPair {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (prefixCode state out : Term ctx) :
 Computes p G outputFrame (prefixCode ::ᵥ HistoryKernel.pairCall ptag state out ::ᵥ nil)
  (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out)) := by
 let args := prefixCode ::ᵥ HistoryKernel.pairCall ptag state out ::ᵥ nil
 have hs := unary p G args (HistoryDecoder.decoder false) (.projection 1) _ _
  (projection p G args 1) (decoder p G ptag hp false state out)
 have ho := unary p G args (HistoryDecoder.decoder true) (.projection 1) _ _
  (projection p G args 1) (decoder p G ptag hp true state out)
 exact binary p G args HistoryCodec.pair _ _ state (HistoryAppend.appendCall atag prefixCode out) _ hs
  (binary p G args HistoryAppend.append (.projection 0) _ prefixCode out _
   (projection p G args 0) ho (copies p G HistoryAppend.append atag ha _))
  (copies p G HistoryCodec.pair ptag hp _)
theorem outputEquation {n ctx : Nat} (p : Program n) (ftag ptag atag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨2,outputFrame⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (prefixCode state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (frameCall ftag prefixCode (HistoryKernel.pairCall ptag state out))
   (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out)))) := by
 obtain ⟨h⟩ := outputAtPair p [] ptag atag hp ha prefixCode state out ftag hf
 exact ⟨h.finish⟩
theorem packedAtPair {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (prefixCode tokens state out : Term ctx) :
 Computes p G packedFrame (prefixCode ::ᵥ HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out) ::ᵥ nil)
  (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out))) := by
 let old := HistoryKernel.pairCall ptag state out
 let args := prefixCode ::ᵥ HistoryKernel.pairCall ptag tokens old ::ᵥ nil
 have hl := unary p G args (HistoryDecoder.decoder false) (.projection 1) _ _
  (projection p G args 1) (decoder p G ptag hp false tokens old)
 have hr := unary p G args (HistoryDecoder.decoder true) (.projection 1) _ _
  (projection p G args 1) (decoder p G ptag hp true tokens old)
 exact binary p G args HistoryCodec.pair _ _ tokens _ _ hl
  (binary p G args outputFrame (.projection 0) _ prefixCode old _
   (projection p G args 0) hr (outputAtPair p G ptag atag hp ha prefixCode state out))
  (copies p G HistoryCodec.pair ptag hp _)
theorem packedEquation {n ctx : Nat} (p : Program n) (ftag ptag atag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨2,packedFrame⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (prefixCode tokens state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (frameCall ftag prefixCode (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)))
   (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out))))) := by
 obtain ⟨h⟩ := packedAtPair p [] ptag atag hp ha prefixCode tokens state out ftag hf
 exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.AtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.AtomsProof
