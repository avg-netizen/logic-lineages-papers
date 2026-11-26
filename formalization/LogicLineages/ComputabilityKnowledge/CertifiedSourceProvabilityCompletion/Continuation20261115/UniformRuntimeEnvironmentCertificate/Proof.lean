module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.ConclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
open HistoryIteratorSuffix.ReconstructionProof
theorem exactCertificate : Targets.InternalRuntimeCertificate := by
 intro arity p old arithmetic x I n inputs e f ctx G raw replacement index fuel hinputs hreplacement
 let T := GorbowPRNumeralCalculation.Theory p
 let template := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let C := UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag template replacement
 let F := conclusion I.ctag I.atag e f raw replacement
 let code := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag template replacement
 obtain ⟨ha⟩ := hreplacement
 obtain ⟨htemplate⟩ := GuardProof.validFormula p old arithmetic x I e f G raw hinputs
 have hg : Hilbert.Local T ctx G (UniformClosedInstanceRecognizer.guards I.fval I.vtag template replacement) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) htemplate) ha
 obtain ⟨hCF⟩ := ConclusionProof.canonical p old arithmetic x I e f G raw hinputs replacement ha
 obtain ⟨hrun⟩ := UniformClosedRule13Certificate.RunProof.internalSingletonRun p old arithmetic x I template replacement index fuel
 obtain ⟨hcore⟩ := UniformClosedRule13Certificate.CoreProof.internalCore p old arithmetic x I template replacement index fuel
 have hr := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hrun) hg
 have hc := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hcore) hg
 have hp := pairCongruence (T := T) (G := G) I.ptag (.zero : Term ctx) C .zero F
  (.base (.logical (.reflexive _))) hCF
 have hcons := pairCongruence (T := T) (G := G) I.ctag
  (HistoryKernel.pairCall I.ptag .zero C) (.zero : Term ctx)
  (HistoryKernel.pairCall I.ptag .zero F) .zero hp (.base (.logical (.reflexive _)))
 have hs := localUnary (.succ (.var 0)) _ _ hcons
 have hs' : Hilbert.Local T ctx G
  (.equal (.succ (HistoryKernel.pairCall I.ctag (HistoryKernel.pairCall I.ptag .zero C) .zero))
   (.succ (HistoryKernel.pairCall I.ctag (HistoryKernel.pairCall I.ptag .zero F) .zero))) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hs
 have ho := pairCongruence (T := T) (G := G) I.ptag
  (.succ (HistoryKernel.pairCall I.ctag (HistoryKernel.pairCall I.ptag .zero C) .zero)) (.zero : Term ctx)
  (.succ (HistoryKernel.pairCall I.ctag (HistoryKernel.pairCall I.ptag .zero F) .zero)) .zero hs'
  (.base (.logical (.reflexive _)))
 have hrunCanonical := localTrans _ _ _ hr ho
 have hd := localUnary (.add (.var 0) (.var 0)) C F hCF
 have hd' : Hilbert.Local T ctx G (.equal (.add C C) (.add F F)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hd
 have hcall : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code)
   (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add F F) code)) := by
  apply callCongruence (T := T) (G := G) I.coreTag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive index))
  | succ i => cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive fuel))
    | succ i => cases i using Fin.cases with
      | zero => exact .base (.logical (.reflexive (.zero : Term ctx)))
      | succ i => cases i using Fin.cases with
        | zero => exact hd'
        | succ i => cases i using Fin.cases with
          | zero => exact .base (.logical (.reflexive code))
          | succ i => exact Fin.elim0 i
 have hcoreCanonical := localTrans _ _ _ (Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) hcall) hc
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.verifierTag I.coreTag (UniformClosedRule13Certificate.checker old arithmetic x) I.h_verifier I.h_core
  index fuel .zero (.add F F) code
 have hfuel := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hcoreCanonical
 have hcf := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hcoreCanonical) hfuel
 have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hrunCanonical) hcf
 exact ⟨hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Proof
