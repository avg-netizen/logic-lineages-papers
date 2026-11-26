module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorInductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.MarkerRejectionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesEliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.CanonicalConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport BoundProof InvariantProof ExpansionCasesSupportProof
/-- All six term constructors, including exclusion of the suppressed marker by
actual complete old scan success; the local IH remains internal. -/
theorem atToken {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (i : Fin 6) (tokens raw oldTail newTail bound rest out : Term ctx)
 (hih : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (allStates ftag stag ptag ctag atag len q l r tokens raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (property ftag stag ptag ctag atag len q l r
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens) raw
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTail)
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 bound) newTail) rest out)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let oldHead : Term ctx := LiteralSyntaxStep.taskCall ptag 0 .zero
 let newHead := LiteralSyntaxStep.taskCall ptag 0 bound
 let oldTasks := HistoryLookup.consCall ctag oldHead oldTail
 let newTasks := HistoryLookup.consCall ctag newHead newTail
 let inputTokens := HistoryLookup.consCall ctag (Term.numeral (n := ctx) i.val) tokens
 let E := EntriesLogic.entries q oldHead oldTasks
 let R := stackRelation len q l r oldTasks newTasks
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks inputTokens) (.succ .zero)
 let Q := Formula.equal (UniformClosedSubstitutionRawFold.foldCall ftag inputTokens
  (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out) raw)
  (final ptag atag rest out inputTokens)
 let Γ := S :: R :: E :: G
 have he0 : Hilbert.Local T ctx Γ E := .hypothesis (by simp [Γ])
 have hr0 : Hilbert.Local T ctx Γ R := .hypothesis (by simp [Γ])
 have hs0 : Hilbert.Local T ctx Γ S := .hypothesis List.mem_cons_self
 have hQ : Nonempty (Hilbert.Local T ctx Γ Q) := by
  by_cases hi : i = 0
  · subst i
    obtain ⟨hm⟩ := MarkerRejectionProof.marker p stag stepTag xtag ptag ctag atag l r dtag
     hs hst hx hp hc ha hl hr hd oldTail tokens
    have hbad := Hilbert.Local.mp (.base hm) hs0
    exact ⟨Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero .zero)))⟩
  · obtain ⟨het⟩ := EntriesEliminationProof.tail p q ctag hq hc oldHead oldHead oldTail
    have hentries := Hilbert.Local.mp (.base het) he0
    obtain ⟨hrt⟩ := TailProof.consTails p len q l r ctag hlen hq hc oldHead oldTail newHead newTail
    have hrel := Hilbert.Local.mp (.base hrt) hr0
    exact ConstructorInductionProof.constructor p Γ ftag stag stepTag etag xtag ptag ctag atag len q l r
     hf hs hst he hx hp hc ha hlen hq hl hr i hi tokens raw oldTail newTail bound rest out
     (push S (push R (push E hih))) hentries hrel hs0
 obtain ⟨hout⟩ := hQ
 exact ⟨hout.discharge.discharge.discharge⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.CanonicalConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.CanonicalConsProof
