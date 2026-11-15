module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- All immediate-prior successful CORE traces survive at identical inputs. -/
theorem retention {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 RetentionCapability p f lhs rhs t old a x I := by
 intro ctx index fuel context formula code
 exact UniformClosedRule13CoreRetention.StatementChecks.exactCoreRetention n p
  LiteralSyntaxValidator.lineValidator (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
  I.previous.current.qctag I.current.coreTag I.previous.previous.previous.pairTag I.previous.previous.previous.consTag
  I.previous.previous.previous.rightTag I.previous.previous.previous.dropTag
  I.previous.current.hqc I.current.h_core I.previous.previous.previous.hp I.previous.previous.previous.hc
  I.previous.previous.previous.hright I.previous.previous.previous.hdrop ctx index fuel context formula code
/-- Quotation validity is unchanged; the exact original certificate is retained. -/
theorem compiler {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (ht : ArithmeticTemplateEvaluation.Arithmetic t) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old a x) : CompilerCapability p f lhs rhs t old a x I := by
 intro ctx values index fuel
 obtain ⟨he⟩ := CumulativeFullFormulaRegistry.CapabilityProof.compiler p f lhs rhs t ht old a x I.previous ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.previous.previous.consTag I.previous.previous.previous.appendTag
  (GorbowPRDefiningEquations.call I.previous.previous.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (GorbowPRDefiningEquations.call I.previous.previous.template.certificateTag values)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hr hc)⟩
theorem equality {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 EqualityCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 obtain ⟨he⟩ := CumulativeFullFormulaRegistry.CapabilityProof.equality p f lhs rhs t old a x I.previous ctx raw index fuel
 let formula := RawEqualityInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag lhs rhs raw
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (RawEqualityInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)
 exact ⟨Hilbert.compose hr he⟩
theorem fullFormula {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 FullFormulaCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 obtain ⟨he⟩ := CumulativeFullFormulaRegistry.CapabilityProof.fullFormula p f lhs rhs t old a x I.previous ctx raw index fuel
 let formula := FullFormulaInstantiation.formulaValue I.previous.current.ctag I.previous.current.atag f raw
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (FullFormulaInstantiationCertificate.certificate I.previous.current.ctag I.previous.current.qtag raw)
 exact ⟨Hilbert.compose hr he⟩
theorem uniform {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 UniformCapability p f lhs rhs t old a x I := by
 intro ctx formula replacement index fuel
 exact UniformClosedRule13Certificate.StatementChecks.exactCertificate n p
  (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.current ctx formula replacement index fuel
/-- One actual installation is selected before all five runtime capabilities. -/
theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro f lhs rhs k t ht old a x
 obtain ⟨I⟩ := InstallationProof.finiteInstallation f lhs rhs t old a x
 exact ⟨I,compiler _ f lhs rhs t ht old a x I,equality _ f lhs rhs t old a x I,
  fullFormula _ f lhs rhs t old a x I,retention _ f lhs rhs t old a x I,uniform _ f lhs rhs t old a x I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.CapabilityProof
