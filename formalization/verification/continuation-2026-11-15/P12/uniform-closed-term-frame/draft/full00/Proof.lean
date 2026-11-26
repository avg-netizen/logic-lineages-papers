module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport RelationalSyntaxDepthTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Exact original guarded framed identity. The internal raw-code induction,
not native syntax reflection, supplies the arbitrary closed runtime traversal. -/
theorem framedClosedIdentity : Targets.InternalFramedClosedIdentity := by
 intro n p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r
  hf he hv hst hs hp hc ha hd hlen hq hl hr ctx tokens bound rest out replacement
 obtain ⟨xtag,hx⟩ := ClosedScanInstallationProof.expandNode p stepTag hst
 let T := GorbowPRNumeralCalculation.Theory p
 let task0 : Term ctx := LiteralSyntaxStep.taskCall ptag 0 .zero
 let taskB : Term ctx := LiteralSyntaxStep.taskCall ptag 0 bound
 let oldTasks := HistoryLookup.consCall ctag task0 .zero
 let newTasks := HistoryLookup.consCall ctag taskB .zero
 obtain ⟨hnil⟩ := EntriesEliminationProof.nil p q hq task0
 obtain ⟨hcons⟩ := EntriesConsProof.cons p q ctag hq hc task0 (.zero : Term ctx)
 have hentries := Derivation.mp hcons hnil
 have hbound : Derivation T (HistoryBounds.weakBound (.zero : Term ctx) bound) :=
  .mp (HistoryBounds.SupportProof.weakIntro .zero bound bound) (Support.equalitySymmetry _ _ (zeroLeft bound))
 obtain ⟨hpair⟩ := ConstructorTaskProof.taskPair p ptag l r 0 hp hl hr (.zero : Term ctx) bound
 have hhead := Derivation.mp hpair hbound
 obtain ⟨hempty⟩ := FullFormulaInstantiationValidity.ClosedTermDepthProof.emptyRelation (ctx := ctx) p len q l r hq
 obtain ⟨hrelcons⟩ := ConsProof.consRelated p len q l r ctag hlen hq hc task0 .zero taskB .zero
 have hrel := Derivation.mp hrelcons (.mp (.mp (.logical (.andIntro _ _)) hhead) hempty)
 obtain ⟨hall⟩ := InductionProof.internalAll p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd tokens replacement oldTasks newTasks rest out
 have hinv := Derivation.mp (.mp hall hentries) hrel
 obtain ⟨hvalid⟩ := RawReflexivityDispatcher.TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc tokens
 have hscan : Derivation T (.imp (RawReflexivityDispatcher.valid vtag tokens)
  (.equal (LiteralSyntaxScan.scanCall stag oldTasks tokens) (.succ .zero))) := by
  simpa only [oldTasks,task0,RawReflexivityDispatcher.TermSoundProof.tasks,
   LiteralNumeralPrefix.termTask,LiteralSyntaxStep.taskCall] using hvalid
 let V := RawReflexivityDispatcher.valid vtag tokens
 have hguard : Hilbert.Local T ctx [V] V := .hypothesis List.mem_cons_self
 have hout := Hilbert.Local.mp (.base hinv) (.mp (.base hscan) hguard)
 obtain ⟨hprefix⟩ := UniformFixedFormulaAgreement.StackProof.appendPrefix p ctag atag hc ha [taskB] rest
 have hpref : Derivation T (.equal (HistoryAppend.appendCall atag newTasks rest)
  (HistoryLookup.consCall ctag taskB rest)) := by
  simpa only [newTasks,FinitePrefixTargets.prefixTerm,UniformFixedFormulaAgreement.StackProof.prepend] using hprefix
 have hstate := ConstructorFrameProof.packedCongruence (T := T) (G := [V]) ptag
  (HistoryAppend.appendCall atag newTasks rest) (HistoryLookup.consCall ctag taskB rest) out (.base hpref)
 have hfold := UniformFixedFormulaAgreement.FoldProof.stateCongruence ftag tokens
  (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out)
  (initial ptag ctag bound rest out) replacement hstate
 exact ⟨(localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hfold) hout).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Proof
