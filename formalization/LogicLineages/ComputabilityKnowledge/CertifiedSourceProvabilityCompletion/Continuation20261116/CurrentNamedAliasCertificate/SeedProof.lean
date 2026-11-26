module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.Membership
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.CoreProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SeedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Actual named-source membership is converted to bounded enumerated membership
before leaf/dispatcher/run/CORE propagation. Not the PR-only seed target. -/
theorem seed {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX)
  f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX)) :
 ∃ seedFuel : Nat, ∀ ctx (larger : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (orderGuard (Term.numeral seedFuel) larger)
   (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag (Term.numeral (Encodable.encode c)) larger .zero
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode (GorbowNamedDefiningTheory.functionAlias (2,0))))
    (Term.numeral (FiniteRuleFourCertificate.certificateCode (GorbowNamedDefiningTheory.functionAlias (2,0))))) (.succ .zero)))) := by
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let q := CumulativePropositionalSource.verifier f lhs rhs old ar baseX
 let logical := CumulativePropositionalSource.logical f lhs rhs old
 let arithmetic := CumulativePropositionalSource.arithmetic ar
 let sigma := GorbowNamedDefiningTheory.functionAlias (2,0)
 let IF := CumulativePropositionalSource.SeedSourceProof.finiteInstallation p f lhs rhs t old ar baseX I
 let dt := FiniteRuleFourCertificate.RunProof.dispatchTag IF.itag logical arithmetic baseX
 have hd := FiniteRuleFourCertificate.RunProof.dispatchInstalled p logical arithmetic baseX IF
 obtain ⟨xt,hx⟩ := FiniteRuleFourDispatcher.InstallationProof.actualLeaf p dt logical arithmetic baseX hd
 obtain ⟨fuel,hiff,hrest⟩ := FiniteSource.Proof.actualFixedFuelPackage pF pR q c hA
 have hb := (hiff sigma).mp (Membership.source pF pR q)
 refine ⟨fuel,?_⟩
 intro ctx larger
 obtain ⟨hl⟩ := FiniteRuleFourLeaf.Proof.largerSeed p xt baseX hx hn c fuel sigma hb ctx larger
 obtain ⟨hlS⟩ := GorbowTheoryProofProof.monotonicity _ _
  (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX) ctx _ ⟨hl⟩
 have hdisp := FiniteRuleFourDispatcher.DispatcherProof.fromLeaf p dt xt logical arithmetic baseX hd hx sigma
  (Term.numeral (Encodable.encode c)) larger .zero
 obtain ⟨hdS⟩ := GorbowTheoryProofProof.monotonicity _ _
  (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX) ctx _ hdisp
 have hrun := FiniteRuleFourCertificate.RunProof.fromDispatcher p logical arithmetic baseX IF sigma
  (Term.numeral (Encodable.encode c)) larger
 obtain ⟨hrS⟩ := GorbowTheoryProofProof.monotonicity _ _
  (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX) ctx _ hrun
 have hcore := FiniteRuleFourCertificate.CoreProof.fromRun p logical arithmetic baseX IF sigma
  (Term.numeral (Encodable.encode c)) larger
 obtain ⟨hcS⟩ := GorbowTheoryProofProof.monotonicity _ _
  (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX) ctx _ hcore
 exact ⟨Hilbert.compose hcS (Hilbert.compose hrS (Hilbert.compose hdS hlS))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SeedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SeedProof
