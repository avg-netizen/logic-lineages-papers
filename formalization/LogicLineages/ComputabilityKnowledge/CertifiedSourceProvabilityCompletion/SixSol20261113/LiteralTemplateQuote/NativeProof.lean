module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.NativeProof
open GorbowSyntax GorbowPRProgram List.Vector
open HistoryRuleSuffix.NativeProof

/-- Structural quotation computes the literal original prefix stream after
numeral substitution. No semantic universal-function evaluation is involved. -/
theorem nativeCalibration : Targets.NativeCalibration := by
 intro k t values
 induction t with
 | var i =>
   change evaluate (HistoryRuleSuffix.applyOne LiteralNumeralPrefix.numeralCode
     (.projection i)) values = _
   rw [oneEval,projectionEval,LiteralNumeralPrefix.NativeProof.nativeCalibration]
   rfl
 | zero =>
   change evaluate (prependToken 1 (HistoryRuleSuffix.constant k 0)) values = _
   rw [prependToken,twoEval,constantEval,constantEval,
     HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
 | succ t ih =>
   change evaluate (prependToken 2 (templateQuote t)) values = _
   rw [prependToken,twoEval,constantEval,ih,
     HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
 | add t u ht hu =>
   change evaluate (prependToken 3
     (HistoryRuleSuffix.applyTwo HistoryAppend.append (templateQuote t) (templateQuote u))) values = _
   rw [prependToken,twoEval,constantEval,twoEval,ht,hu,appendList,
     HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
 | mul t u ht hu =>
   change evaluate (prependToken 4
     (HistoryRuleSuffix.applyTwo HistoryAppend.append (templateQuote t) (templateQuote u))) values = _
   rw [prependToken,twoEval,constantEval,twoEval,ht,hu,appendList,
     HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
 | universalFunction t ih =>
   change evaluate (prependToken 5 (templateQuote t)) values = _
   rw [prependToken,twoEval,constantEval,ih,
     HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.NativeProof
