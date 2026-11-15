module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport.ConstructorStepTargets
theorem prefixSame {ctx : Nat} (ctag : Nat) (xs : List (Term ctx)) :
 FinitePrefixTargets.prefixTerm ctag xs =
 RelationalSyntaxDepthTransport.FinitePrefixTargets.prefixTerm ctag xs := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  simp only [FinitePrefixTargets.prefixTerm,
   RelationalSyntaxDepthTransport.FinitePrefixTargets.prefixTerm,ih]
theorem rowsUnchanged {ctx : Nat} (ptag : Nat) (depth : Term ctx)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) :
 RowProof.newRows ptag depth ctor = tasks ptag depth ctor := by
 cases ctor with
 | term i =>
  fin_cases i <;> first
   | exact False.elim (hmarker rfl)
   | rfl
 | formula i => rfl
/-- Actual singleton emitted chunk and original constructor scan, with related
child prefixes/tails. Both new-stack transition and relation are constructed. -/
theorem nonMarker {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag stepTag stag ptag ctag atag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (depth oldTail newTail raw : Term ctx)
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r oldTail newTail)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (resultBody stag len q l r
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) depth) newTail)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral (kind ctor)) (.succ depth) oldTail)
    (Term.numeral (token ctor)) raw)
   (output ptag ctag atag ctor (.succ depth) oldTail)
   (output ptag ctag atag ctor depth newTail))) := by
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨hrow⟩ := RelationalSyntaxDepthTransport.ConstructorStepProof.stepAt
  p stepTag xtag ptag ctag atag hstep hx hp hc ha ctor depth newTail
 obtain ⟨hscan⟩ := ScanProof.singleton p G stag stepTag ptag ctag hs hstep hp hc
  (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) depth) newTail)
  (Term.numeral (token ctor)) (output ptag ctag atag ctor depth newTail) (.base hrow)
 obtain ⟨hemit⟩ := EmitterProof.constructor p etag ptag ctag he hp hc ctor hmarker (.succ depth) oldTail raw
 have heq := UniformSubstitutionIndexValidity.BranchProof.scanCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := G) stag
  (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) depth) newTail) _ _ (.base hemit)
 have hout := localTrans _ _ _ heq hscan
 have hrows := RowProof.rows p G ptag l r hp hl hr ctor depth
 rw [rowsUnchanged ptag depth ctor hmarker] at hrows
 obtain ⟨hrel⟩ := FinitePrefixProof.finitePrefixAppend n p len q l r ctag atag hlen hq hc ha
  ctx G (tasks ptag (.succ depth) ctor) (tasks ptag depth ctor) oldTail newTail hrows ⟨hrest⟩
 have hrel' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r (output ptag ctag atag ctor (.succ depth) oldTail)
   (output ptag ctag atag ctor depth newTail)) := by
  simpa only [output,prefixSame] using hrel
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hout) hrel'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConstructorProof
