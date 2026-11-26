module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.RepeatedProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
theorem exactRepeated : Targets.InternalRepeatedSpecialization := by
 intro arity p old arithmetic x I mtag hm n
 induction n with
 | zero =>
  intro f ctx G raw antecedent index fuel hinputs
  dsimp only
  intro ha
  let T := GorbowPRNumeralCalculation.Theory p
  let C : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))
  let B := value I.ctag I.atag f raw
  obtain ⟨ha⟩ := ha
  obtain ⟨he⟩ := BaseProof.emptyValue p I.ctag I.atag I.h_ctag I.h_atag f raw
  have hab : Hilbert.Local T ctx G (.equal C B) :=
   Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) (.base he)
  obtain ⟨hc⟩ := BaseProof.coreTransport T G I.coreTag index fuel C B antecedent hab ha
  obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
   p I.verifierTag I.coreTag (UniformClosedRule13Certificate.checker old arithmetic x) I.h_verifier I.h_core
   index fuel .zero (.add B B) antecedent
  have hf := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hc
  exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf⟩
 | succ n ih =>
  intro f ctx G raw antecedent index fuel hinputs
  dsimp only
  intro ha
  have ht : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hinputs i.succ
  have hh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (Continuation20261114.RawReflexivityDispatcher.valid I.vtag raw.head)) := by
   simpa only [List.Vector.get_zero] using hinputs 0
  obtain ⟨htail⟩ := ih (.all f) ctx G raw.tail antecedent index fuel ht ha
  have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) htail
  rw [EnvironmentProof.allValue] at hcore
  obtain ⟨hout⟩ := UniformRuntimeSpecializationStep.StatementChecks.exactSpecializationStep
   arity p old arithmetic x I mtag hm (n+1) n (headEnvironment n) f ctx G raw.tail raw.head
   (certificate mtag I.ctag I.atag I.constructorTag (.all f) raw.tail antecedent)
   index fuel ht hh ⟨hcore⟩
  simpa only [certificate,EnvironmentProof.stepValue] using (Nonempty.intro hout)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.RepeatedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.RepeatedProof
