module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CompilerCapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem compiler {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (ht : ArithmeticTemplateEvaluation.Arithmetic t) (old a : Program 1) (x : Program 3)
 (pF pR : Program 1) (I : JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : CompilerCapability f lhs rhs t old a x pF pR I := by
 let p := root f lhs rhs pF pR old a x
 intro ctx values index fuel
 obtain ⟨he⟩ := CumulativeUniformRule12Registry.CapabilityProof.compiler p f lhs rhs t ht old a (SaturatedAxiomLeaf.saturated x) I.previous ctx values index fuel
 have hv := Derivation.mp (.logical (.andLeft _ _)) he
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 let formula := RawEqualityComposition.eqRaw I.previous.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.previous.appendTag
  (GorbowPRDefiningEquations.call I.previous.previous.previous.previous.template.quoteTag values)
  (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
 obtain ⟨hr⟩ := CapabilitySupport.retentionInternal p f lhs rhs t old a (SaturatedAxiomLeaf.saturated x) I index fuel .zero (.add formula formula)
  (GorbowPRDefiningEquations.call I.previous.previous.previous.previous.template.certificateTag values)
 exact CapabilitySupport.inSource f lhs rhs pF pR old a x _ ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hr hc)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CompilerCapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CompilerCapabilityProof
