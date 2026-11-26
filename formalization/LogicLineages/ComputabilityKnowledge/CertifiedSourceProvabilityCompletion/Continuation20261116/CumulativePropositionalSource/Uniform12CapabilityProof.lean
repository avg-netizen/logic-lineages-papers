module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform12CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CapabilitySupport
theorem uniform12 {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Uniform12Capability f lhs rhs t old a baseX pF pR I := by
 intro ctx formula left right index fuel
 let p := root f lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let J := I.previous.current
 let A := UniformClosedRule12.guards J.fval J.vtag formula left right
 let C := UniformClosedRule12.conclusionValue J.caseTag J.predTag J.ctag formula left right
 let code := UniformClosedRule12Certificate.certificate J.ctag J.constructorTag formula left right
 obtain ⟨hcert⟩ := CumulativeUniformRule12Registry.CapabilityProof.uniform12 p f lhs rhs t old a _ I.previous ctx formula left right index fuel
 have hh : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hall := Hilbert.Local.mp (.base hcert) hh
 have hrun := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hall
 have hcf := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hall
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcf
 obtain ⟨hrr⟩ := UniformClosedPropositionalCoreRetention.Generic.Iteration.Proof.internalIteratorRetention
  (UniformClosedPropositional.recognizer false) (UniformClosedPropositional.recognizer true)
  4 p LiteralSyntaxValidator.lineValidator (previousLogical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  J.iteratorTag I.currentK.iteratorTag J.ptag J.ctag J.h_iterator I.currentK.h_iteratorTag J.h_ptag J.h_ctag
  ctx code (HistoryRunSplice.state J.ptag (.succ .zero) code) index fuel
  (HistoryLookup.consCall J.ctag (HistoryKernel.pairCall J.ptag .zero C) .zero) .zero
 have hnewRun := Hilbert.Local.mp (.base hrr) hrun
 obtain ⟨hret⟩ := retentionInternal p f lhs rhs t old a _ I index fuel .zero (.add C C) code
 have hnew := Hilbert.Local.mp (.base hret) hcore
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.currentK.verifierTag I.currentK.coreTag
  (UniformClosedPropositionalCertificate.checker (previousLogical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX))
  I.currentK.h_verifierTag I.currentK.h_coreTag index fuel .zero (.add C C) code
 have hfuel := Hilbert.Local.mp (.base hinj) hnew
 have hnewcf := Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) hnew) hfuel
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) hnewRun) hnewcf
 exact inSource f lhs rhs pF pR old a baseX _ ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform12CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform12CapabilityProof
