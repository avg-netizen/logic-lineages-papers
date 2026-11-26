module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SegmentProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph UniformClosedSubstitutionRawFold
/-- Finite literal input prefix with arbitrary symbolic tail, not arbitrary-list exhaustion. -/
def tokenPrefix {ctx : Nat} (ctag : Nat) : List Nat → Term ctx → Term ctx
 | [], tail => tail
 | a::xs, tail => HistoryLookup.consCall ctag (Term.numeral a) (tokenPrefix ctag xs tail)
theorem segment {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (xs : List Nat) (tokens state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (tokenPrefix ctag xs tokens) state raw)
   (foldCall ftag tokens (foldCall ftag (tokenPrefix ctag xs .zero) state raw) raw))) := by
 induction xs generalizing state with
 | nil =>
  obtain ⟨hr0,hi,hllen⟩ := InstallationProof.installed p ftag hf
  obtain ⟨hz⟩ := Proof.nilFold p ftag ptag _ _ _ hf hp hi hllen hr0 state raw
  exact ⟨Support.equalitySymmetry _ _ (FoldProof.stateCongruence ftag tokens _ state raw hz)⟩
 | cons a xs ih =>
  let newState := FoldProof.next ptag stag etag atag ltag rtag (Term.numeral a) state raw
  obtain ⟨hleft⟩ := FoldProof.consAny p ftag ptag ctag stag etag atag ltag rtag
   hf hp hc hs he ha hl hr (Term.numeral a) (tokenPrefix ctag xs tokens) state raw
  obtain ⟨hind⟩ := ih newState
  obtain ⟨hright⟩ := FoldProof.consAny p ftag ptag ctag stag etag atag ltag rtag
   hf hp hc hs he ha hl hr (Term.numeral a) (tokenPrefix ctag xs .zero) state raw
  have houter := FoldProof.stateCongruence ftag tokens _ _ raw hright
  exact ⟨Logic.trans _ _ _ hleft (Logic.trans _ _ _ hind (Support.equalitySymmetry _ _ houter))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SegmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SegmentProof
