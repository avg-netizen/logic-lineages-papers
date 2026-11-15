module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.VariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.BranchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof UniformClosedSubstitutionEmit.InternalAtomsProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
noncomputable def scanCongruence {ctx : Nat} {T : Sentence → Prop} {G : List (Formula ctx)} stag (tasks a b : Term ctx)
 (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (LiteralSyntaxScan.scanCall stag tasks a) (LiteralSyntaxScan.scanCall stag tasks b)) := by
 apply callCongruence (T := T) (G := G) stag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact .base (.logical (.reflexive tasks))
 | succ i => cases i using Fin.cases with
   | zero => exact h
   | succ i => exact Fin.elim0 i
theorem below {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag stag ptag ctag dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (index depth gap rest raw : Term ctx)
 (hgap : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add index (.succ gap)) depth)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (termTasks ptag ctag depth)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) index raw)) (.succ .zero))) := by
 have hdepth := successorDepth p G ptag ctag hp hc (Term.numeral 2) depth rest index raw
 have hindex := UniformClosedSubstitutionEmit.IndexProof.belowCase p G ctag hc _ index depth gap raw hdepth hgap
 obtain ⟨hemit⟩ := UniformClosedSubstitutionEmit.IndexProof.enterIndex p G ptag ctag hp hc (.succ depth) rest index raw _ hindex etag he
 obtain ⟨hpositive⟩ := UniformClosedSubstitutionEmit.ArithmeticProof.differenceBelow p G index depth gap hgap dtag hd
 obtain ⟨hscan⟩ := VariableProof.exactVariable n p stag ptag ctag dtag hs hp hc hd ctx index depth gap
 have hvalid := Hilbert.Local.mp (.base hscan) hpositive
 exact ⟨localTrans _ _ _ (scanCongruence stag (termTasks ptag ctag depth) _ _ hemit) hvalid⟩
theorem equalIndex {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag vtag stag ptag ctag atag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (depth rest raw : Term ctx)
 (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (termTasks ptag ctag depth)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) depth raw)) (.succ .zero))) := by
 have hdepth := successorDepth p G ptag ctag hp hc (Term.numeral 2) depth rest depth raw
 have hindex := UniformClosedSubstitutionEmit.IndexProof.equalCase p G _ depth raw hdepth
 obtain ⟨hemit⟩ := UniformClosedSubstitutionEmit.IndexProof.enterIndex p G ptag ctag hp hc (.succ depth) rest depth raw _ hindex etag he
 obtain ⟨hscan⟩ := FullFormulaInstantiationValidity.ClosedTermDepthStatementChecks.exactClosedTermAtAnyDepth
  n p vtag stag ptag ctag atag hv hs hp hc ha ctx depth raw
 exact ⟨localTrans _ _ _ (scanCongruence stag (termTasks ptag ctag depth) _ _ hemit) (.mp (.base hscan) hvalid)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.BranchProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.BranchProof
