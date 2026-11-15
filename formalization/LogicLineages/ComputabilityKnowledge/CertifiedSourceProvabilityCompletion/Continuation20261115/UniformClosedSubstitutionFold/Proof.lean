module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.IterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.DispatcherSupportProof
theorem runCongruence {ctx : Nat} {T : Theory} tag (count a b raw : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (iterateCall tag count a raw) (iterateCall tag count b raw)) := by
 apply Hilbert.Local.finish
 apply callCongruence (T := T) (G := []) tag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact .base (.logical (.reflexive count))
 | succ i => cases i using Fin.cases with
   | zero => exact .base h
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i
theorem exactFiniteFold : Targets.InternalFiniteFold := by
 intro n p itag ptag ctag stag etag atag hi hp hc hs he ha ctx tokens state out raw
 induction tokens generalizing state out with
 | nil => exact IterationProof.zero p itag hi _ raw
 | cons token tokens ih =>
  obtain ⟨hf⟩ := IterationProof.firstNumeral p itag hi tokens.length
   (HistoryKernel.pairCall ptag (tokenTerms ctag (token::tokens)) (HistoryKernel.pairCall ptag state out)) raw
  obtain ⟨ht⟩ := TickProof.tickCons p ptag ctag stag etag atag hp hc hs he ha token
   (tokenTerms ctag tokens) state out raw (IterationProof.tickTag itag) (IterationProof.tickInstalled p itag hi)
  have hm := runCongruence itag (Term.numeral tokens.length) _ _ raw ht.finish
  obtain ⟨hr⟩ := ih (LiteralSyntaxStep.stepCall stag state token)
   (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))
  exact ⟨Logic.trans _ _ _ hf (Logic.trans _ _ _ hm hr)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Proof
