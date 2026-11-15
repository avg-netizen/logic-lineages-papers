module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113

theorem internalArithmetic : Targets.InternalArithmetic := by
 intro k t h n p old a x I J ctx values index fuel
 obtain ⟨he⟩ := ArithmeticTemplateEvaluation.StatementChecks.exactEvaluation k t h n p old a x I.toArithmetic J ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 obtain ⟨ht⟩ := RawUniversalCoreRetention.StatementChecks.exactCoreRetention n p
  LiteralSyntaxValidator.lineValidator (RawUniversalCongruence.previousLogical old) (RawMulNewestAddition.arithmetic a) x
  I.qctag I.universalCoreTag I.pairTag I.consTag I.rightTag I.dropTag I.hqc I.huniversalCore I.hp I.hc I.hright I.hdrop
  ctx index fuel .zero
  (.add (RawUniversalCongruence.eqRaw I.consTag I.appendTag
   (GorbowPRDefiningEquations.call J.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values)))
   (RawUniversalCongruence.eqRaw I.consTag I.appendTag
   (GorbowPRDefiningEquations.call J.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))))
  (GorbowPRDefiningEquations.call J.certificateTag values)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp ht hc)⟩

theorem internalUniversalArgument : Targets.InternalUniversalArgument := by
 intro k t h n p old a x I J ctx values index fuel
 obtain ⟨he⟩ := internalArithmetic k t h n p old a x I J ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.validatorTag I.hv
 obtain ⟨hscan⟩ := LiteralNumeralPrefix.StatementChecks.exactScan n p I.numeralTag stag I.pairTag I.consTag I.hnumeral hs I.hp I.hc ctx
  (ArithmeticTemplateEvaluation.instantiatedValue t values) .zero .zero
 obtain ⟨hn⟩ := RawSuccCongruence.ValidityProof.localBinding p [] I.validatorTag stag I.pairTag I.consTag I.hv hs I.hp I.hc
  (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values)) (.base hscan)
 have hn' := Hilbert.Local.finish hn
 obtain ⟨hu⟩ := RawUniversalCongruence.StatementChecks.exactCongruence n p old a x I ctx
  (GorbowPRDefiningEquations.call J.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
  (GorbowPRDefiningEquations.call J.certificateTag values) index fuel
 exact ⟨.mp (.mp (.mp hu hv) hn') hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Proof.internalArithmetic
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.Proof.internalUniversalArgument
