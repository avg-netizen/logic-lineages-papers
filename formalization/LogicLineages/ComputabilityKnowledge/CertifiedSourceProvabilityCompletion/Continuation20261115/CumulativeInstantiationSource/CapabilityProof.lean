module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem compiler {k : Nat} (lhs rhs : Term 1) (t : Term k) (ht : ArithmeticTemplateEvaluation.Arithmetic t)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeInstantiationRegistry.JointInstallation (root lhs rhs pF pR old a baseX)
  lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 CompilerCapability lhs rhs t old a baseX pF pR I := by
 intro ctx values index fuel
 let p := root lhs rhs pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 obtain ⟨he⟩ := UniversalArgumentEvaluation.StatementChecks.exactArithmetic k t ht 4 p old a x I.previous I.template ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.consTag I.previous.appendTag
  (GorbowPRDefiningEquations.call I.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨hr⟩ := EqualityInstantiationCoreRetention.StatementChecks.exactCoreRetention lhs rhs 4 p
  LiteralSyntaxValidator.lineValidator (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x
  I.previous.universalCoreTag I.current.qctag I.previous.pairTag I.previous.consTag I.previous.rightTag I.previous.dropTag
  I.previous.huniversalCore I.current.hqc I.previous.hp I.previous.hc I.previous.hright I.previous.hdrop
  ctx index fuel .zero (.add formula formula) (GorbowPRDefiningEquations.call I.template.certificateTag values)
 have hout := Derivation.mp (Derivation.mp (.logical (.andIntro _ _)) hv) (.mp hr hc)
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ ⟨hout⟩
theorem instantiation {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeInstantiationRegistry.JointInstallation (root lhs rhs pF pR old a baseX)
  lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 InstantiationCapability lhs rhs t old a baseX pF pR I := by
 intro ctx raw index fuel
 have hout := RawEqualityInstantiationCertificate.StatementChecks.exactCore lhs rhs 4
  (root lhs rhs pF pR old a baseX) (CumulativeInstantiationRegistry.previousLogical old)
  (RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX) I.current ctx raw index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.CapabilityProof
