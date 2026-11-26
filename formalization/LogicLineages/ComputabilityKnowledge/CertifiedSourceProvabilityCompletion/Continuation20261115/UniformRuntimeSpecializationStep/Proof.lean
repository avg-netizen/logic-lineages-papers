module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
theorem exactStep : Targets.InternalSpecializationStep := by
 intro arity p old arithmetic x I mtag hm n inputs e f ctx G raw replacement antecedent index fuel hinputs hr
 dsimp only
 intro hant
 let T := GorbowPRNumeralCalculation.Theory p
 let A := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let U := FixedFormulaSubstitution.unaryValue I.ctag 10 A
 let B := body I.ctag I.atag e f raw replacement
 let impCode := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag A replacement
 let code := certificate mtag I.ctag I.atag I.constructorTag e f raw replacement antecedent
 obtain ⟨hc⟩ := UniformRuntimeEnvironmentCertificate.StatementChecks.exactRuntimeCertificate
  arity p old arithmetic x I n inputs e f ctx G raw replacement index fuel hinputs hr
 have hcf := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hc
 have himp := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcf
 have himp' : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero
   (.add (LiteralRawMP.implicationRaw I.atag I.ctag U B)
    (LiteralRawMP.implicationRaw I.atag I.ctag U B)) impCode) (.succ .zero)) := by
  exact himp
 obtain ⟨ha⟩ := hant
 have hinput : Hilbert.Local T ctx G
  (LiteralCoreMP.inputAcceptance I.coreTag I.atag I.ctag .zero U B impCode antecedent index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) himp') ha
 have hd := InstallationProof.dropNode p old arithmetic x I
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP
  (UniformClosedRule13.logicalLeaf old) arithmetic x arity p
  I.iteratorTag I.len I.atag I.ptag I.ctag I.rtag (HistoryLookup.LookupProof.dropTag I.qtag)
  I.qtag I.dispatcherTag I.h_iterator I.h_len I.h_atag I.h_ptag I.h_ctag I.h_rtag hd I.h_qtag I.h_dispatcher
  mtag I.coreTag hm I.h_core ctx .zero U B impCode antecedent index fuel
 have hout : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add B B) code) (.succ .zero)) :=
  Hilbert.Local.mp (Hilbert.Local.base hmp) hinput
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.verifierTag I.coreTag (UniformClosedRule13Certificate.checker old arithmetic x) I.h_verifier I.h_core
  index fuel .zero (.add B B) code
 have hfuel := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hout
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hout) hfuel⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Proof
