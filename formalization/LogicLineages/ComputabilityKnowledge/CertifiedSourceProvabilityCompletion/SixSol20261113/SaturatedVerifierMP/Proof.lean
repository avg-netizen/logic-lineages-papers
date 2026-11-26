module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel LiteralRawMP LiteralMPRun LiteralValidatedMPRun

/-- Both order witnesses are actual internal additive gaps. No evaluation or
external inequality enters the arithmetic derivation. -/
noncomputable def leftBound {T : Sentence → Prop} {ctx : Nat} (s t : Term ctx) :
 Derivation T (orderGuard s (.add s t)) :=
 .mp (FuelWitness.ExtractionLogicProof.orderIntro s (.add s t) t) (.logical (.reflexive (.add s t)))
noncomputable def rightBound {T : Sentence → Prop} {ctx : Nat} (s t : Term ctx) :
 Derivation T (orderGuard t (.add s t)) :=
 .mp (FuelWitness.ExtractionLogicProof.orderIntro t (.add s t) s) (HistoryCodec.ArithmeticSupport.addComm t s)

theorem internalVerifierMP : Targets.InternalVerifierMP := by
 intro l a baseX n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag hi hl ha hp hc hd hdrop hr hdispatch
 intro mtag qtag vtag hm hq hv ctx context phi psi imp ant index s t
 let T := GorbowPRNumeralCalculation.Theory p
 let x := SaturatedAxiomLeaf.saturated baseX
 let rawImp := implicationRaw atag ctag phi psi
 let fullImp := Term.add rawImp rawImp
 let fullAnt := Term.add phi phi
 let fullOut := Term.add psi psi
 let resultCert := certificate mtag context psi imp ant
 let sum := Term.add s t
 let H := SaturatedVerifierMP.inputAcceptance vtag atag ctag context phi psi imp ant index s t
 obtain ⟨heImp⟩ := SaturatedVerifierCore.StatementChecks.internalEquivalence validity l a baseX n p vtag qtag hv hq ctx index s context fullImp imp
 obtain ⟨heAnt⟩ := SaturatedVerifierCore.StatementChecks.internalEquivalence validity l a baseX n p vtag qtag hv hq ctx index t context fullAnt ant
 obtain ⟨heOut⟩ := SaturatedVerifierCore.StatementChecks.internalEquivalence validity l a baseX n p vtag qtag hv hq ctx index sum context fullOut resultCert
 obtain ⟨hmImp⟩ := SaturatedCoreFuel.StatementChecks.internalMonotonicity validity l a baseX n p qtag hq ctx index s sum context fullImp imp
 obtain ⟨hmAnt⟩ := SaturatedCoreFuel.StatementChecks.internalMonotonicity validity l a baseX n p qtag hq ctx index t sum context fullAnt ant
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP l a x n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag
  hi hl ha hp hc hd hdrop hr hdispatch mtag qtag hm hq ctx context phi psi imp ant index sum
 have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have outerImp : Hilbert.Local T ctx [H] (success vtag index s context fullImp imp) := .mp (.base (.logical (.andLeft _ _))) h
 have outerAnt : Hilbert.Local T ctx [H] (success vtag index t context fullAnt ant) := .mp (.base (.logical (.andRight _ _))) h
 have coreImp := Hilbert.Local.mp (.mp (.base (.logical (.andLeft _ _))) (.base heImp)) outerImp
 have coreAnt := Hilbert.Local.mp (.mp (.base (.logical (.andLeft _ _))) (.base heAnt)) outerAnt
 have alignedImp := Hilbert.Local.mp (.mp (.base hmImp) (.base (leftBound s t))) coreImp
 have alignedAnt := Hilbert.Local.mp (.mp (.base hmAnt) (.base (rightBound s t))) coreAnt
 have both : Hilbert.Local T ctx [H] (LiteralCoreMP.inputAcceptance qtag atag ctag context phi psi imp ant index sum) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) alignedImp) alignedAnt
 have coreOut := Hilbert.Local.mp (.base hmp) both
 have outerOut := Hilbert.Local.mp (.mp (.base (.logical (.andRight _ _))) (.base heOut)) coreOut
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge outerOut)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Proof
