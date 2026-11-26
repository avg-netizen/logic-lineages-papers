module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.AllCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph
/-- Genuine current-CORE case13, with its opaque predecessor conclusion
normalized by the guarded original substitution-negation theorem. -/
theorem negated {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (a w index fuel : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.currentK.fval I.previous.previous.current.vtag a w)) :
 let J := RuntimeRebase.shared p f lhs rhs t old ar x I
 let V := J.previous.previous.current.toDispatcherInstallation.toInstallation
 let neg := CurrentNegatedInstanceBridge.negValue V.ctag
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (impValue V.ctag V.atag (FixedFormulaSubstitution.unaryValue V.ctag 10 (neg a))
    (neg (CurrentNegatedInstanceBridge.instanceValue V a w)))
   (UniformClosedRule13Certificate.certificate V.ctag J.previous.previous.current.constructorTag (neg a) w))) := by
 let J := RuntimeRebase.shared p f lhs rhs t old ar x I
 let V : UniformClosedRule13Validity.Installation p := J.previous.previous.current.toDispatcherInstallation.toInstallation
 obtain ⟨hng⟩ := CurrentNegatedInstanceBridge.InstanceProof.negGuard p V G a w hg
 obtain ⟨hcert⟩ := CumulativeUniformRule12Registry.CapabilityProof.uniform13 p f lhs rhs t old ar x J.previous
  ctx (CurrentNegatedInstanceBridge.negValue V.ctag a) w index fuel
 have hac := Hilbert.Local.mp (.base hcert) hng
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hac
 obtain ⟨hret⟩ := CumulativePropositionalSource.CapabilitySupport.retentionInternal p f lhs rhs t old ar x J index fuel .zero _ _
 have hnew := Hilbert.Local.mp (.base hret) hcore
 obtain ⟨hbridge⟩ := CurrentNegatedInstanceBridge.StatementChecks.exactInternal n p V ctx a w
 have heq := Hilbert.Local.mp (.base (.logical (.andRight _ _))) (Hilbert.Local.mp (.base hbridge) hg)
 exact LogicProof.coreFormula I.currentK.coreTag index fuel _ _ _ heq hnew
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.AllCore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.AllCore
