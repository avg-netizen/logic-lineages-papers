module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.AtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
theorem atPair {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (tokens state out : Term ctx) :
 Computes p G eraseCode (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out) ::ᵥ nil)
  (HistoryKernel.pairCall ptag tokens state) := by
 let old := HistoryKernel.pairCall ptag state out
 let args := HistoryKernel.pairCall ptag tokens old ::ᵥ nil
 have hl := decoder p G ptag hp false tokens old
 have hr := decoder p G ptag hp true tokens old
 have hs : Computes p G syntaxProjection args state :=
  unary p G args (HistoryDecoder.decoder false) (HistoryDecoder.decoder true) old state hr
   (decoder p G ptag hp false state out)
 exact binary p G args HistoryCodec.pair (HistoryDecoder.decoder false) syntaxProjection
  tokens state _ hl hs (copies p G HistoryCodec.pair ptag hp _)
theorem equation {n ctx : Nat} (p : Program n) etag ptag
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (tokens state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (eraseCall etag (HistoryKernel.pairCall ptag tokens (HistoryKernel.pairCall ptag state out)))
   (HistoryKernel.pairCall ptag tokens state))) := by
 obtain ⟨h⟩ := atPair p [] ptag hp tokens state out etag he
 exact ⟨h.finish⟩
/-- Arbitrary numeric packed states are reconstructed internally, not assumed
to come from a native pair/list encoding. -/
theorem reconstruct {n ctx : Nat} (p : Program n) (ptag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (packed : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryKernel.pairCall ptag (call ltag (packed ::ᵥ nil))
   (HistoryKernel.pairCall ptag (call ltag (call rtag (packed ::ᵥ nil) ::ᵥ nil))
    (call rtag (call rtag (packed ::ᵥ nil) ::ᵥ nil)))) packed)) := by
 obtain ⟨houter⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction n p ptag ltag rtag hp hl hr ctx packed
 obtain ⟨hinner⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction n p ptag ltag rtag hp hl hr ctx (call rtag (packed ::ᵥ nil))
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := [])
  ptag (call ltag (packed ::ᵥ nil)) _ (call ltag (packed ::ᵥ nil)) (call rtag (packed ::ᵥ nil))
  (.base (.logical (.reflexive _))) (.base hinner)
 exact ⟨Logic.trans _ _ _ hpair.finish houter⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.AtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.AtomsProof
