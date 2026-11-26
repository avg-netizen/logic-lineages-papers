module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.StepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.RepeatedProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeSpecialization
theorem repeated {arity k : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x) :
 ∀ n (f : Formula n) ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n)
 (antecedent index fuel : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) →
 let C := Term.numeral (n := ctx) (Encodable.encode
  (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.universalClosure f)))
 let B := value I.previous.current.ctag I.previous.current.atag f raw
 let code := certificate I.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag I.previous.current.constructorTag f raw antecedent
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (SixSol20261113.LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add C C) antecedent) (.succ .zero))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj (.equal (SixSol20261113.LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add B B) code))) := by
 intro n
 let J := I.previous.current
 let mtag := I.previous.previous.previous.previous.mpTag
 induction n with
 | zero =>
  intro f ctx G raw antecedent index fuel hinputs
  dsimp only
  intro ha
  let T := GorbowPRNumeralCalculation.Theory p
  let C : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))
  let B := value J.ctag J.atag f raw
  obtain ⟨ha⟩ := ha
  obtain ⟨he⟩ := BaseProof.emptyValue p J.ctag J.atag J.h_ctag J.h_atag f raw
  have hab : Hilbert.Local T ctx G (.equal C B) :=
   Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) (.base he)
  obtain ⟨hc⟩ := BaseProof.coreTransport T G I.current.coreTag index fuel C B antecedent hab ha
  obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
   p I.current.verifierTag I.current.coreTag (UniformClosedRule12Certificate.checker
    (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
    (Continuation20261114.RawMulNewestAddition.arithmetic a) x) I.current.h_verifier I.current.h_core
   index fuel .zero (.add B B) antecedent
  have hf := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hc
  exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf⟩
 | succ n ih =>
  intro f ctx G raw antecedent index fuel hinputs
  dsimp only
  intro ha
  have ht : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (Continuation20261114.RawReflexivityDispatcher.valid J.vtag (raw.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hinputs i.succ
  have hh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (Continuation20261114.RawReflexivityDispatcher.valid J.vtag raw.head)) := by
   simpa only [List.Vector.get_zero] using hinputs 0
  obtain ⟨htail⟩ := ih (.all f) ctx G raw.tail antecedent index fuel ht ha
  have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) htail
  rw [EnvironmentProof.allValue] at hcore
  obtain ⟨hout⟩ := StepProof.step p installed lhs rhs t old a x I (n+1) n (headEnvironment n) f ctx G raw.tail raw.head
   (certificate mtag J.ctag J.atag J.constructorTag (.all f) raw.tail antecedent)
   index fuel ht hh ⟨hcore⟩
  simpa only [certificate,EnvironmentProof.stepValue] using (Nonempty.intro hout)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.RepeatedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.RepeatedProof
