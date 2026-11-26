module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual same-root program copies only; no success, calibration or image fields.
Tags may name duplicate copies and are not silently identified. -/
structure GraphInstallation {n : Nat} (p : Program n) where
 caseTag : Nat
 predTag : Nat
 itag : Nat
 ftag : Nat
 fval : Nat
 vtag : Nat
 ptag : Nat
 ctag : Nat
 rtag : Nat
 len : Nat
 htag : Nat
 ttag : Nat
 atag : Nat
 h_caseTag : (nodes p)[caseTag]? = some ⟨1,UniformClosedCase12.caseCode⟩
 h_predTag : (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩
 h_itag : (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩
 h_ftag : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩
 h_fval : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 h_vtag : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 h_ptag : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 h_ctag : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 h_rtag : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩
 h_len : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩
 h_htag : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩
 h_ttag : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩
 h_atag : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
/-- Additional actual scanner/emit/lookup nodes used by the already checked
arbitrary-runtime substitution output-validity theorem. -/
structure Installation {n : Nat} (p : Program n) extends GraphInstallation p where
 etag : Nat
 stepTag : Nat
 stag : Nat
 dtag : Nat
 qtag : Nat
 ltag : Nat
 h_etag : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩
 h_stepTag : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩
 h_stag : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩
 h_dtag : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩
 h_qtag : (nodes p)[qtag]? = some ⟨2,HistoryLookup.lookup⟩
 h_ltag : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩

def compiledConclusion {n ctx : Nat} {p : Program n} (I : GraphInstallation p)
 (formula left right : Term ctx) : Term ctx :=
 UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula left right
def expandedConclusion {n ctx : Nat} {p : Program n} (I : GraphInstallation p)
 (formula left right : Term ctx) : Term ctx :=
 UniformClosedCase12.formulaValue I.ctag I.atag left right
  (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag formula left)
  (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag formula right)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity
