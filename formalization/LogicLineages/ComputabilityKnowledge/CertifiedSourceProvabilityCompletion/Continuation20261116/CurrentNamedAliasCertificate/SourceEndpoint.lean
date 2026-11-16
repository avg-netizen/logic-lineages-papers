module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SpecializationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.RuntimeInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.EncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph

theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX))
 (aliasTag : Nat)
 (hp : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX))[aliasTag]? = some ⟨2,program⟩) :
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 ∃ seedFuel : Nat, ∀ ctx (r s larger : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (orderGuard (Term.numeral seedFuel) larger)
   (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) larger
    (aliasCode (tags R.previous) r s) (call aliasTag (r ::ᵥ s ::ᵥ nil))))) := by
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX)
 let incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX
 let J := RuntimeInterface.tags R
 let K := tags R.previous
 have HJ := RuntimeInterface.installed R
 have HK := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) R
 obtain ⟨seedFuel,hseed⟩ := SpecializationProof.specialized f lhs rhs t old ar baseX pF pR c hA hn R
 refine ⟨seedFuel,?_⟩
 intro ctx r s larger
 let H := orderGuard (Term.numeral seedFuel) larger
 let G := [H]
 let raw := LiteralNumeralPrefix.numeralCall K.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag s ::ᵥ nil
 have hg : Hilbert.Local U ctx G H := .hypothesis List.mem_cons_self
 have hvalid (a : Term ctx) : Nonempty (Hilbert.Local U ctx G
  (RawReflexivityDispatcher.valid R.previous.previous.current.vtag (LiteralNumeralPrefix.numeralCall K.numeralTag a))) := by
  obtain ⟨hv⟩ := ValidityProof.numeral p _ _ _ I.previous.current K.numeralTag HK.hn [] a
  obtain ⟨hvS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hv.finish⟩
  exact ⟨.base hvS⟩
 have hinputs : ∀ i, Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid R.previous.previous.current.vtag (raw.get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hvalid r
  | succ i => cases i using Fin.cases with
   | zero => exact hvalid s
   | succ i => exact Fin.elim0 i
 obtain ⟨hs⟩ := hseed ctx G raw larger hinputs ⟨hg⟩
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 obtain ⟨he⟩ := EncodingProof.matrixCode p K HK r s
 obtain ⟨heS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨he⟩
 obtain ⟨hc⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula R.currentK.coreTag
  (Term.numeral (Encodable.encode c)) larger _ _ _ (.base heS) hcore
 obtain ⟨hgraph⟩ := GraphProof.graph p (r ::ᵥ s ::ᵥ nil) J HJ aliasTag hp
 obtain ⟨hgraphS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hgraph⟩
 obtain ⟨hcode⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U G R.currentK.coreTag
  (Term.numeral (Encodable.encode c)) larger _ _ _ (.base (Support.equalitySymmetry _ _ hgraphS)) hc
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX)
  R U incl G _ _ (Term.numeral (Encodable.encode c)) larger hcode
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.SourceEndpoint
