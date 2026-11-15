module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- All old accepted CORE traces at this same actual root survive. -/
theorem retention {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 RetentionCapability p f lhs rhs t old a x I := by
 intro ctx index fuel context formula code
 exact FullFormulaInstantiationCoreRetention.StatementChecks.exactCoreRetention f n p
  LiteralSyntaxValidator.lineValidator (previousLogical lhs rhs old) (RawMulNewestAddition.arithmetic a) x
  I.previous.current.qctag I.current.qctag I.previous.previous.pairTag I.previous.previous.consTag
  I.previous.previous.rightTag I.previous.previous.dropTag
  I.previous.current.hqc I.current.hqc I.previous.previous.hp I.previous.previous.hc
  I.previous.previous.hright I.previous.previous.hdrop ctx index fuel context formula code
/-- Original arithmetic certificate compiler, through both checked extensions. -/
theorem compiler {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (ht : ArithmeticTemplateEvaluation.Arithmetic t) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old a x) : CompilerCapability p f lhs rhs t old a x I := by
 intro ctx values index fuel
 obtain ⟨he⟩ := UniversalArgumentEvaluation.StatementChecks.exactArithmetic k t ht n p old a x
  I.previous.previous I.previous.template ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.previous.consTag I.previous.previous.appendTag
  (GorbowPRDefiningEquations.call I.previous.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨heq⟩ := EqualityInstantiationCoreRetention.StatementChecks.exactCoreRetention lhs rhs n p
  LiteralSyntaxValidator.lineValidator (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x
  I.previous.previous.universalCoreTag I.previous.current.qctag I.previous.previous.pairTag I.previous.previous.consTag
  I.previous.previous.rightTag I.previous.previous.dropTag
  I.previous.previous.huniversalCore I.previous.current.hqc I.previous.previous.hp I.previous.previous.hc
  I.previous.previous.hright I.previous.previous.hdrop
  ctx index fuel .zero (.add formula formula) (GorbowPRDefiningEquations.call I.previous.template.certificateTag values)
 obtain ⟨hfull⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (GorbowPRDefiningEquations.call I.previous.template.certificateTag values)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hfull (.mp heq hc))⟩
theorem equality {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 EqualityCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 obtain ⟨heq⟩ := RawEqualityInstantiationCertificate.StatementChecks.exactCore lhs rhs n p
  (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x I.previous.current ctx raw index fuel
 let formula := RawEqualityInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag lhs rhs raw
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (RawEqualityInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)
 exact ⟨Hilbert.compose hr heq⟩
theorem fullFormula {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 FullFormulaCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 exact FullFormulaInstantiationCertificate.StatementChecks.exactInternalCore f n p
  (previousLogical lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.current ctx raw index fuel
/-- One chosen concrete installation precedes all runtime capability arguments. -/
theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro f lhs rhs k t ht old a x
 obtain ⟨I⟩ := InstallationProof.finiteInstallation f lhs rhs k t old a x
 exact ⟨I,compiler _ f lhs rhs t ht old a x I,equality _ f lhs rhs t old a x I,
  fullFormula _ f lhs rhs t old a x I,retention _ f lhs rhs t old a x I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.CapabilityProof
