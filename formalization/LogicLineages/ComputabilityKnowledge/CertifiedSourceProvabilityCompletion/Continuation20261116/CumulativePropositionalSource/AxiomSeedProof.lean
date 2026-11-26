module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.AxiomSeedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem seed {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (verifier installed lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX) installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 SeedCapability installed lhs rhs t old a baseX pF pR c I := by
 let IF := SeedSourceProof.finiteInstallation _ installed lhs rhs t old a baseX I
 obtain ⟨fuel,hseed⟩ := FiniteRuleFourCertificate.StatementChecks.exactFiniteLiteralCertificate
  (logical installed lhs rhs old) (arithmetic a) baseX pF pR c hA hn IF
 refine ⟨fuel,?_⟩
 intro sigma hmem ctx larger
 obtain ⟨_,⟨hc⟩,⟨hf⟩⟩ := hseed sigma hmem ctx larger
 let T := S pF pR (verifier installed lhs rhs old a baseX)
 let H := SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) (.mp (.base hc) hh)) (.mp (.base hf) hh)
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.AxiomSeedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.AxiomSeedProof
