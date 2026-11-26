module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open UniformRuntimeSpecializationStep
/-- Retain only the generated Rule13 instance; consume the antecedent directly
at current CORE. There is no backwards transport of the input certificate. -/
theorem step {arity k : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p installed lhs rhs t old a x) :
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (replacement antecedent index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag replacement)) →
 let U := FixedFormulaSubstitution.unaryValue I.previous.previous.current.ctag 10
  (FixedFormulaSubstitution.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag raw f e)
 let B := body I.previous.previous.current.ctag I.previous.previous.current.atag e f raw replacement
 let code := certificate I.previous.previous.previous.previous.previous.mpTag I.previous.previous.current.ctag I.previous.previous.current.atag I.previous.previous.current.constructorTag e f raw replacement antecedent
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add U U) antecedent) (.succ .zero))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.currentK.verifierTag index fuel .zero (.add B B) code))) := by
 intro n inputs e f ctx G raw replacement antecedent index fuel hinputs hr
 let J := I.previous.previous.current
 let mtag := I.previous.previous.previous.previous.previous.mpTag
 have hm := I.previous.previous.previous.previous.previous.hmp
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
 obtain ⟨hret⟩ := SeedSourceProof.priorRetentionInternal
  p installed lhs rhs t old a x I index fuel .zero
  (.add (UniformRuntimeEnvironmentCertificate.conclusion J.ctag J.atag e f raw replacement)
   (UniformRuntimeEnvironmentCertificate.conclusion J.ctag J.atag e f raw replacement)) impCode
 have himp := Hilbert.Local.mp (.base hret) hold
 have himp' : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero
   (.add (LiteralRawMP.implicationRaw J.atag J.ctag U B)
    (LiteralRawMP.implicationRaw J.atag J.ctag U B)) impCode) (.succ .zero)) := by
  exact himp
 obtain ⟨ha⟩ := hant
 have hinput : Hilbert.Local T ctx G
  (LiteralCoreMP.inputAcceptance I.currentK.coreTag J.atag J.ctag .zero U B impCode antecedent index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) himp') ha
 have hd := UniformRuntimeSpecializationStep.InstallationProof.dropNode p
  (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) x J
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP
  (CumulativePropositionalSource.logical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) x arity p
  I.currentK.iteratorTag J.len J.atag J.ptag J.ctag J.rtag (HistoryLookup.LookupProof.dropTag J.qtag)
  J.qtag I.currentK.dispatcherTag I.currentK.h_iteratorTag J.h_len J.h_atag J.h_ptag J.h_ctag J.h_rtag hd J.h_qtag I.currentK.h_dispatcherTag
  mtag I.currentK.coreTag hm I.currentK.h_coreTag ctx .zero U B impCode antecedent index fuel
 have hout : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add B B) code) (.succ .zero)) :=
  Hilbert.Local.mp (Hilbert.Local.base hmp) hinput
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.currentK.verifierTag I.currentK.coreTag (UniformClosedPropositionalCertificate.checker
   (CumulativePropositionalSource.previousLogical installed lhs rhs old)
   (Continuation20261114.RawMulNewestAddition.arithmetic a) x) I.currentK.h_verifierTag I.currentK.h_coreTag
  index fuel .zero (.add B B) code
 have hfuel := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hout
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hout) hfuel⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedStepProof
