module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.OutputProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.GuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateInstance
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Paid actual instance predecessor and output-fold agreement, not an
assumed substitution identity. Only genuine closed-coordinate guards enter. -/
theorem instantiated {arity n inputs ctx : Nat} (p : Program arity) (old ar : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old ar x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (w : Term ctx)
 (hraw : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (hw : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag w)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (CurrentNegatedInstanceBridge.instanceValue I.toDispatcherInstallation.toInstallation
    (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e) w)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (w ::ᵥ raw) f (UniformRuntimeEnvironmentAgreement.specialize e)))) := by
 obtain ⟨hf⟩ := UniformRuntimeEnvironmentCertificate.GuardProof.validFormula p old ar x I e f G raw hraw
 have hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.fval I.vtag (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e) w) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hf) hw
 obtain ⟨hi⟩ := CurrentNegatedInstanceBridge.InstanceProof.actualOutput p I.toDispatcherInstallation.toInstallation G _ w hg
 obtain ⟨ho⟩ := UniformRuntimeEnvironmentCertificate.OutputProof.substituted p old ar x I e f G raw hraw w
 exact ⟨localTrans _ _ _ hi ho⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateInstance
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateInstance
