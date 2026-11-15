module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceSupportProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.CertificateGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowFormulaSubstitution FixedFormulaSubstitution List.Vector SixSol20261113
open TraceSupportProof
theorem exactTrace : Targets.InternalPrescribedTrace := by
 intro arity p old arithmetic x I mtag hm n
 induction n with
 | zero =>
  intro f sigma ctx antecedent
  exact ⟨.logical (.reflexive _)⟩
 | succ n ih =>
  intro f sigma ctx antecedent
  let B := substituteFormula (liftSubstitute (fun i => sigma i.succ)) f
  let A := formulaValue I.ctag I.atag (numeralInputs (ctx := ctx) (fun i => sigma i.succ)) f (headEnvironment n)
  obtain ⟨hA⟩ := EncodingProof.formula (ctx := ctx) p I.ctag I.atag I.h_ctag I.h_atag
   (headEnvironment n) f (fun i => sigma i.succ)
  rw [assignmentHead] at hA
  obtain ⟨hbody⟩ := EncodingProof.formula (ctx := ctx) p I.ctag I.atag I.h_ctag I.h_atag
   (runtimeEnvironment (n+1)) f sigma
  rw [assignmentRuntime] at hbody
  have hs := EnvironmentProof.stepValue I.ctag I.atag f (numeralInputs (ctx := ctx) sigma)
  rw [tailInputs,headInputs] at hs
  have hb : Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (UniformRuntimeSpecializationStep.body I.ctag I.atag (headEnvironment n) f
    (numeralInputs (ctx := ctx) (fun i => sigma i.succ))
    (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (sigma 0)))))
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula sigma f))))) := by
   rw [hs]
   exact hbody
  obtain ⟨himp⟩ := CertificateGraphProof.singleton p I.ctag I.constructorTag I.h_ctag I.h_constructor
   A B (sigma 0) hA
  obtain ⟨hant⟩ := ih (.all f) (fun i => sigma i.succ) ctx antecedent
  have hout := CertificateGraphProof.mp p mtag hm _ _ _ (substituteFormula sigma f)
   (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.allInstantiate B (sigma 0))])
   (produce (.all f) (fun i => sigma i.succ) antecedent) hb himp hant
  simpa only [certificate,tailInputs,headInputs,UniformRuntimeSpecializationStep.certificate,produce] using hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.TraceProof
