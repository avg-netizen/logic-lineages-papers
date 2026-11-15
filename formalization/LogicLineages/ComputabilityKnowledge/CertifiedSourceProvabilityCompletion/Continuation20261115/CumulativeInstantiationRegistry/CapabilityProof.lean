module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem compiler {k : Nat} (lhs rhs : Term 1) (t : Term k) (ht : ArithmeticTemplateEvaluation.Arithmetic t)
 (old a : Program 1) (x : Program 3)
 (I : JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x) :
 CompilerCapability lhs rhs t old a x I := by
 intro ctx values index fuel
 let p := carrier lhs rhs t old a x
 obtain ⟨he⟩ := UniversalArgumentEvaluation.StatementChecks.exactArithmetic k t ht 6 p old a x I.previous I.template ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.consTag I.previous.appendTag
  (GorbowPRDefiningEquations.call I.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨hr⟩ := EqualityInstantiationCoreRetention.StatementChecks.exactCoreRetention lhs rhs 6 p
  LiteralSyntaxValidator.lineValidator (previousLogical old) (RawMulNewestAddition.arithmetic a) x
  I.previous.universalCoreTag I.current.qctag I.previous.pairTag I.previous.consTag I.previous.rightTag I.previous.dropTag
  I.previous.huniversalCore I.current.hqc I.previous.hp I.previous.hc I.previous.hright I.previous.hdrop
  ctx index fuel .zero (.add formula formula) (GorbowPRDefiningEquations.call I.template.certificateTag values)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hr hc)⟩
theorem instantiation {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x) :
 InstantiationCapability lhs rhs t old a x I := by
 intro ctx raw index fuel
 exact RawEqualityInstantiationCertificate.StatementChecks.exactCore lhs rhs 6
  (carrier lhs rhs t old a x) (previousLogical old) (RawMulNewestAddition.arithmetic a) x I.current ctx raw index fuel

theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro lhs rhs k t ht old a x
 obtain ⟨I⟩ := InstallationProof.finiteInstallation lhs rhs k t old a x
 exact ⟨I,compiler lhs rhs t ht old a x I,instantiation lhs rhs t old a x I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.CapabilityProof
