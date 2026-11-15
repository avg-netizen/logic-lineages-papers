module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SegmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SequenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph UniformClosedSubstitutionRawFold
open SegmentProof
/-- Literal input order agrees with original list concatenation. -/
theorem prefixAppend {ctx : Nat} (ctag : Nat) (xs ys : List Nat) (tail : Term ctx) :
 tokenPrefix ctag (xs ++ ys) tail = tokenPrefix ctag xs (tokenPrefix ctag ys tail) := by
 induction xs with
 | nil => rfl
 | cons a xs ih => simp only [List.cons_append, tokenPrefix, ih]
/-- Private sequencing of proved actual fold equations, used by syntax
induction. No supplied equation survives the final agreement target. -/
theorem compose {n ctx : Nat} (p : Program n) (ftag ptag ctag stag etag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)


 (xs ys : List Nat) (state middle finalState raw : Term ctx)
 (hfirst : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (tokenPrefix ctag xs .zero) state raw) middle))
 (hsecond : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (tokenPrefix ctag ys .zero) middle raw) finalState)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (foldCall ftag (tokenPrefix ctag (xs ++ ys) .zero) state raw) finalState)) := by
 rw [prefixAppend]
 obtain ⟨hseg⟩ := segment p ftag ptag ctag stag etag atag ltag rtag hf hp hc hs he ha hl hr
  xs (tokenPrefix ctag ys .zero) state raw
 have hcng := FoldProof.stateCongruence ftag (tokenPrefix ctag ys .zero) _ middle raw hfirst
 exact ⟨Logic.trans _ _ _ hseg (Logic.trans _ _ _ hcng hsecond)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SequenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SequenceProof
