module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual same-root prior/current checker memberships; drop is recovered
from the supplied lookup AST, not added as an installation premise. -/
theorem retention {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 RetentionCapability p f lhs rhs t old a x I := by
 intro ctx index fuel context formula code
 have hd := SixSol20261112.Fuel.Equations.argumentChild p I.current.qtag HistoryLookup.reference
  (fun _ : Fin 1 => HistoryLookup.drop) I.current.h_qtag 0
 exact UniformClosedRule12CoreRetention.StatementChecks.exactCoreRetention n p
  LiteralSyntaxValidator.lineValidator (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
  I.previous.current.coreTag I.current.coreTag I.current.ptag I.current.ctag I.current.rtag
  (HistoryLookup.LookupProof.dropTag I.current.qtag)
  I.previous.current.h_core I.current.h_core I.current.h_ptag I.current.h_ctag I.current.h_rtag hd
  ctx index fuel context formula code
/-- Quotation validity is unchanged; the exact original certificate is retained. -/
theorem compiler {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (ht : ArithmeticTemplateEvaluation.Arithmetic t) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old a x) : CompilerCapability p f lhs rhs t old a x I := by
 intro ctx values index fuel
 obtain ⟨he⟩ := CumulativeUniformRule13Registry.CapabilityProof.compiler p f lhs rhs t ht old a x I.previous ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.appendTag
  (GorbowPRDefiningEquations.call I.previous.previous.previous.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (GorbowPRDefiningEquations.call I.previous.previous.previous.template.certificateTag values)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hr hc)⟩
theorem equality {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 EqualityCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 obtain ⟨he⟩ := CumulativeUniformRule13Registry.CapabilityProof.equality p f lhs rhs t old a x I.previous ctx raw index fuel
 let formula := RawEqualityInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag lhs rhs raw
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (RawEqualityInstantiationCertificate.certificate I.previous.previous.previous.current.ctag I.previous.previous.previous.current.qtag raw)
 exact ⟨Hilbert.compose hr he⟩
theorem fullFormula {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) :
 FullFormulaCapability p f lhs rhs t old a x I := by
 intro ctx raw index fuel
 obtain ⟨he⟩ := CumulativeUniformRule13Registry.CapabilityProof.fullFormula p f lhs rhs t old a x I.previous ctx raw index fuel
 let formula := FullFormulaInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag f raw
 obtain ⟨hr⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add formula formula)
  (FullFormulaInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)
 exact ⟨Hilbert.compose hr he⟩
theorem uniform13 {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Uniform13Capability p f lhs rhs t old a x I := by
 intro ctx formula replacement index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let A := UniformClosedInstanceRecognizer.guards I.previous.current.fval I.previous.current.vtag formula replacement
 let C := UniformClosedRule13.conclusionValue I.previous.current.caseTag I.previous.current.predTag I.previous.current.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag formula replacement
 obtain ⟨hcert⟩ := UniformClosedRule13Certificate.StatementChecks.exactCertificate n p
  (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.previous.current ctx formula replacement index fuel
 have hh : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hall := Hilbert.Local.mp (.base hcert) hh
 have hcf := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hall
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcf
 obtain ⟨hret⟩ := retention p f lhs rhs t old a x I ctx index fuel .zero (.add C C) code
 have hnew := Hilbert.Local.mp (.base hret) hcore
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.current.verifierTag I.current.coreTag
  (UniformClosedRule12Certificate.checker (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x)
  I.current.h_verifier I.current.h_core index fuel .zero (.add C C) code
 have hfuel := Hilbert.Local.mp (.base hinj) hnew
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) hnew) hfuel
 exact ⟨hout.discharge.finish⟩
theorem uniform12 {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Uniform12Capability p f lhs rhs t old a x I := by
 intro ctx formula left right index fuel
 exact UniformClosedRule12Certificate.StatementChecks.exactCertificate n p
  (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.current ctx formula left right index fuel
/-- One joint actual installation precedes all six runtime capabilities. -/
theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro f lhs rhs k t ht old a x
 obtain ⟨I⟩ := InstallationProof.finiteInstallation f lhs rhs t old a x
 exact ⟨I,compiler _ f lhs rhs t ht old a x I,equality _ f lhs rhs t old a x I,
  fullFormula _ f lhs rhs t old a x I,retention _ f lhs rhs t old a x I,
  uniform13 _ f lhs rhs t old a x I,uniform12 _ f lhs rhs t old a x I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry.CapabilityProof
