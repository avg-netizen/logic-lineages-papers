module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.CanonicalConsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermCasesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ActualConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport BoundProof InvariantProof ExpansionCasesSupportProof
open LiteralRawMP.DispatcherSupportProof
/-- No canonical head or native token is assumed: actual entries, decoder
reconstruction, and all successful expansion arms supply them internally. -/
theorem actual {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
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
 (token tokens raw oldHead oldTail newHead newTail rest out added : Term ctx)
 (hih : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (allStates ftag stag ptag ctag atag len q l r tokens raw))
 (hentries : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) (HistoryLookup.consCall ctag oldHead oldTail)))
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r (HistoryLookup.consCall ctag oldHead oldTail) (HistoryLookup.consCall ctag newHead newTail)))
 (hex : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall xtag oldHead token) (.succ added)))
 (hscan : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag oldHead oldTail)
   (HistoryLookup.consCall ctag token tokens)) (.succ .zero))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall ftag (HistoryLookup.consCall ctag token tokens)
   (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag
    (HistoryLookup.consCall ctag newHead newTail) rest)) out) raw)
   (final ptag atag rest out (HistoryLookup.consCall ctag token tokens)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let oldTask : Term ctx := LiteralSyntaxStep.taskCall ptag 0 .zero
 let bound := call r (newHead ::ᵥ nil)
 let newTask := LiteralSyntaxStep.taskCall ptag 0 bound
 let oldTasks := HistoryLookup.consCall ctag oldHead oldTail
 let newTasks := HistoryLookup.consCall ctag newHead newTail
 let inputTokens := HistoryLookup.consCall ctag token tokens
 let Q := Formula.equal (UniformClosedSubstitutionRawFold.foldCall ftag inputTokens
  (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out) raw)
  (final ptag atag rest out inputTokens)
 obtain ⟨hhead⟩ := EntriesEliminationProof.head p q ctag hq hc oldTask oldHead oldTail
 have ho := Hilbert.Local.mp (.base hhead) hentries
 have hleft := callCongruence (T := T) (G := G) l (oldHead ::ᵥ nil) (oldTask ::ᵥ nil) (fun i => by
  cases i using Fin.cases with
  | zero => exact ho
  | succ i => exact Fin.elim0 i)
 obtain ⟨hdecoder⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (.zero : Term ctx) .zero
 have hk0 : Hilbert.Local T ctx G (.equal (call l (oldHead ::ᵥ nil)) .zero) := localTrans _ _ _ hleft (.base hdecoder)
 obtain ⟨hheads⟩ := HeadProof.consHeads p len q l r ctag hq hc oldHead oldTail newHead newTail
 have hheadrel := Hilbert.Local.mp (.base hheads) hrel
 have hkind := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hheadrel
 have hknew := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hkind) hk0
 obtain ⟨hn⟩ := StepTransportTaskProof.canonical p G ptag l r 0 hp hl hr newHead hknew
 have holdRow := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := G) ctag
  oldTask oldTail oldHead oldTail (HistoryOrder.StepProof.localSym _ _ ho) (.base (.logical (.reflexive oldTail)))
 have hnewRow := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := G) ctag
  newTask newTail newHead newTail (HistoryOrder.StepProof.localSym _ _ hn) (.base (.logical (.reflexive newTail)))
 have hterms : ∀ i : Fin 6, Nonempty (Hilbert.Local T ctx G (.imp (.equal token (Term.numeral i.val)) Q)) := by
  intro i
  let H := Formula.equal token (Term.numeral i.val)
  have ht : Hilbert.Local T ctx (H :: G) H := .hypothesis List.mem_cons_self
  obtain ⟨hcanonical⟩ := CanonicalConsProof.atToken p (H :: G) ftag stag stepTag etag xtag ptag ctag atag len q l r
   hf hs hst he hx hp hc ha hlen hq hl hr dtag hd i tokens raw oldTail newTail bound rest out (push H hih)
  have hp1 := Hilbert.Local.mp (.mp (.base (TransportProof.oldTasks ftag stag ptag ctag atag len q l r
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens) raw
   (HistoryLookup.consCall ctag oldTask oldTail) oldTasks (HistoryLookup.consCall ctag newTask newTail) rest out))
   (push H holdRow)) hcanonical
  have hp2 := Hilbert.Local.mp (.mp (.base (TransportProof.newTasks ftag stag ptag ctag atag len q l r
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens) raw oldTasks
   (HistoryLookup.consCall ctag newTask newTail) newTasks rest out)) (push H hnewRow)) hp1
  have htokRow := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := H :: G) ctag
   (Term.numeral i.val) tokens token tokens (HistoryOrder.StepProof.localSym _ _ ht) (.base (.logical (.reflexive tokens)))
  have hp3 := Hilbert.Local.mp (.mp (.base (transportTokens ftag stag ptag ctag atag len q l r
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens) inputTokens raw oldTasks newTasks rest out)) htokRow) hp2
  have hout := Hilbert.Local.mp (.mp (.mp hp3 (push H hentries)) (push H hrel)) (push H hscan)
  exact ⟨hout.discharge⟩
 exact TermCasesProof.eliminate p G xtag ptag ctag dtag l r hx hp hc hd hl hr oldHead token added Q hk0 hex hterms
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ActualConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ActualConsProof
