module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.BoundProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermRowsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorStepTargets BoundProof
/-- Genuine positive constructor case of the raw-code induction. All supplied
local hypotheses are the changing invariant and its actual tail IH, not a new
public assumption. Selection of a non-marker term constructor is discharged
by successful raw-step classification in the final assembly. -/
theorem constructor {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
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
 (i : Fin 6) (hi : i ≠ 0) (tokens raw oldTail newTail bound rest out : Term ctx)
 (hih : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (allStates ftag stag ptag ctag atag len q l r tokens raw))
 (hentries : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTail))
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r oldTail newTail))
 (hscan : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTail)
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens)) (.succ .zero))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall ftag
   (HistoryLookup.consCall ctag (Term.numeral i.val) tokens)
   (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag
    (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 bound) newTail) rest)) out) raw)
   (final ptag atag rest out (HistoryLookup.consCall ctag (Term.numeral i.val) tokens)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let oldNext := output ptag ctag atag (.term i) (.zero : Term ctx) oldTail
 let newNext := output ptag ctag atag (.term i) bound newTail
 let out' := HistoryAppend.appendCall atag out (HistoryLookup.consCall ctag (Term.numeral (n := ctx) i.val) .zero)
 have hbound : Derivation T (HistoryBounds.weakBound (.zero : Term ctx) bound) :=
  .mp (HistoryBounds.SupportProof.weakIntro .zero bound bound) (Support.equalitySymmetry _ _ (zeroLeft bound))
 obtain ⟨hpair⟩ := ConstructorStepProof.constructorStepPair n p stepTag xtag ptag ctag atag len q l r
  hst hx hp hc ha hlen hq hl hr ctx (.term i) .zero bound oldTail newTail
 have hrows := Hilbert.Local.mp (.mp (.base hpair) (.base hbound)) hrel
 have holdstep := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrows
 have hrestrows := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrows
 have hrelNext := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrestrows
 obtain ⟨hscanCons⟩ := UniformSubstitutionFoldTransport.ScanProof.cons p G stag stepTag ptag ctag hs hst hp hc
  (Term.numeral i.val) tokens (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTail) oldNext holdstep
 have hscanNext := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hscanCons) hscan
 obtain ⟨heNext⟩ := TermRowsProof.outputEntries p q ptag ctag atag hq hc ha i hi oldTail
 have hentriesNext := Hilbert.Local.mp (.base heNext) hentries
 have h1 := Hilbert.Local.mp (.base (allStatesInstance ftag stag ptag ctag atag len q l r tokens raw oldNext)) hih
 have h2 := Hilbert.Local.mp (.base (allPrefixesInstance ftag stag ptag ctag atag len q l r tokens raw oldNext newNext)) h1
 have h3 := Hilbert.Local.mp (.base (allRestsInstance ftag stag ptag ctag atag len q l r tokens raw oldNext newNext rest)) h2
 have h4 := Hilbert.Local.mp (.base (allOutputsInstance ftag stag ptag ctag atag len q l r tokens raw oldNext newNext rest out')) h3
 have htail := Hilbert.Local.mp (.mp (.mp h4 hentriesNext) hrelNext) hscanNext
 have hmarker : Constructor.term i ≠ .term 0 := by intro h; cases h; exact hi rfl
 obtain ⟨hconsume⟩ := ConstructorFrameProof.consumes p ftag ptag ctag stepTag etag atag xtag l r
  hf hp hc hst he ha hx hl hr (.term i) hmarker bound newTail rest tokens out raw
 obtain ⟨houtput⟩ := UniformFixedFormulaAgreement.OutputProof.tokenThen p atag ctag l r ha hc hl hr out (Term.numeral i.val) tokens
 have hfinal := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := G) ptag
  (.succ rest) (HistoryAppend.appendCall atag out' tokens) (.succ rest)
  (HistoryAppend.appendCall atag out (HistoryLookup.consCall ctag (Term.numeral i.val) tokens))
  (.base (.logical (.reflexive (.succ rest)))) (.base houtput)
 exact ⟨localTrans _ _ _ (.base hconsume) (localTrans _ _ _ htail hfinal)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorInductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ConstructorInductionProof
