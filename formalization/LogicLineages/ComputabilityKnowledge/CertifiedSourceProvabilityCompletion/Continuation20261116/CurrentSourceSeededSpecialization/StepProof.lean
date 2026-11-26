module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.SourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open UniformRuntimeSpecializationStep
/-- Retain only the generated Rule13 instance; consume the antecedent directly
at current CORE. There is no backwards transport of the input certificate. -/
theorem step {arity k : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x) :
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (replacement antecedent index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag replacement)) →
 let U := FixedFormulaSubstitution.unaryValue I.previous.current.ctag 10
  (FixedFormulaSubstitution.formulaValue I.previous.current.ctag I.previous.current.atag raw f e)
 let B := body I.previous.current.ctag I.previous.current.atag e f raw replacement
 let code := certificate I.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag I.previous.current.constructorTag e f raw replacement antecedent
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add U U) antecedent) (.succ .zero))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add B B) code))) := by
 intro n inputs e f ctx G raw replacement antecedent index fuel hinputs hr
 let J := I.previous.current
 let mtag := I.previous.previous.previous.previous.mpTag
 have hm := I.previous.previous.previous.previous.hmp
 dsimp only
 intro hant
 let T := GorbowPRNumeralCalculation.Theory p
 let A := FixedFormulaSubstitution.formulaValue J.ctag J.atag raw f e
 let U := FixedFormulaSubstitution.unaryValue J.ctag 10 A
 let B := body J.ctag J.atag e f raw replacement
 let impCode := UniformClosedRule13Certificate.certificate J.ctag J.constructorTag A replacement
 let code := certificate mtag J.ctag J.atag J.constructorTag e f raw replacement antecedent
 obtain ⟨hc⟩ := UniformRuntimeEnvironmentCertificate.StatementChecks.exactRuntimeCertificate
  arity p (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) x J n inputs e f ctx G raw replacement index fuel hinputs hr
 have hcf := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hc
 have hold := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcf
 obtain ⟨hret⟩ := CumulativeUniformRule12Registry.CapabilityProof.retention
  p installed lhs rhs t old a x I ctx index fuel .zero
  (.add (UniformRuntimeEnvironmentCertificate.conclusion J.ctag J.atag e f raw replacement)
   (UniformRuntimeEnvironmentCertificate.conclusion J.ctag J.atag e f raw replacement)) impCode
 have himp := Hilbert.Local.mp (.base hret) hold
 have himp' : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (LiteralRawMP.implicationRaw J.atag J.ctag U B)
    (LiteralRawMP.implicationRaw J.atag J.ctag U B)) impCode) (.succ .zero)) := by
  exact himp
 obtain ⟨ha⟩ := hant
 have hinput : Hilbert.Local T ctx G
  (LiteralCoreMP.inputAcceptance I.current.coreTag J.atag J.ctag .zero U B impCode antecedent index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) himp') ha
 have hd := UniformRuntimeSpecializationStep.InstallationProof.dropNode p
  (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) x J
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP
  (CumulativeUniformRule12Source.logical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) x arity p
  I.current.iteratorTag J.len J.atag J.ptag J.ctag J.rtag (HistoryLookup.LookupProof.dropTag J.qtag)
  J.qtag I.current.dispatcherTag I.current.h_iterator J.h_len J.h_atag J.h_ptag J.h_ctag J.h_rtag hd J.h_qtag I.current.h_dispatcher
  mtag I.current.coreTag hm I.current.h_core ctx .zero U B impCode antecedent index fuel
 have hout : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add B B) code) (.succ .zero)) :=
  Hilbert.Local.mp (Hilbert.Local.base hmp) hinput
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.current.verifierTag I.current.coreTag (UniformClosedRule12Certificate.checker
   (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
   (Continuation20261114.RawMulNewestAddition.arithmetic a) x) I.current.h_verifier I.current.h_core
  index fuel .zero (.add B B) code
 have hfuel := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hout
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hout) hfuel⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.StepProof
