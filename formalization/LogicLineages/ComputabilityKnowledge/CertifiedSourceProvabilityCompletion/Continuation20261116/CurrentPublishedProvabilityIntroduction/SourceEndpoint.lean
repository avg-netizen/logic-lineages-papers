module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeEndpoint
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph

theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX)
  f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar (SaturatedAxiomLeaf.saturated baseX))
 (N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX))
 (transformTag publishedTag : Nat)
 (ht : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX))[transformTag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩)
 (hp : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX))[publishedTag]? = some ⟨7,program⟩) :
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 ∀ (sigma : Sentence) ctx (innerFuel innerCertificate inputProof index outerFuel : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (accepted R.currentK.coreTag R.currentK.verifierTag index outerFuel
    (checkerEquationCode (tags R.previous) pF c sigma innerFuel innerCertificate) inputProof)
   (accepted R.currentK.coreTag R.currentK.verifierTag index outerFuel
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
    (outputCode publishedTag pF c sigma innerFuel innerCertificate inputProof)))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 dsimp only
 intro sigma ctx innerFuel innerCertificate inputProof index outerFuel
 let H := accepted R.currentK.coreTag R.currentK.verifierTag index outerFuel
  (checkerEquationCode (tags R.previous) pF c sigma innerFuel innerCertificate) inputProof
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨hout⟩ := RuntimeEndpoint.current p f lhs rhs t rawOld ar (SaturatedAxiomLeaf.saturated baseX) I N transformTag publishedTag ht hp
  pF c sigma [H] innerFuel innerCertificate inputProof index outerFuel hc
 exact GorbowTheoryProofProof.monotonicity _ _ (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX)
  ctx _ ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceEndpoint
