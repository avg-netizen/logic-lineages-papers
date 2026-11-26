module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.AliasProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX)) :
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 ∃ seedFuel : Nat, ∀ ctx (r s larger : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (orderGuard (Term.numeral seedFuel) larger)
   (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) larger
    (CurrentNamedAliasCertificate.aliasCode (tags R.previous) r s)
     (aliasCertificate (tags R.previous) R.previous.previous.current.constructorTag r s)))) := by
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX)
 let incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX
 let J := CurrentNamedAliasCertificate.RuntimeInterface.tags R
 let K := tags R.previous
 have HJ := CurrentNamedAliasCertificate.RuntimeInterface.installed R
 have HK := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) R
 obtain ⟨seedFuel,hseed⟩ := CurrentNamedAliasCertificate.SpecializationProof.specialized f lhs rhs t old ar baseX pF pR c hA hn R
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
 obtain ⟨he⟩ := CurrentNamedAliasCertificate.EncodingProof.matrixCode p K HK r s
 obtain ⟨heS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨he⟩
 obtain ⟨hc⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula R.currentK.coreTag
  (Term.numeral (Encodable.encode c)) larger _ _ _ (.base heS) hcore
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX)
  R U incl G _ _ (Term.numeral (Encodable.encode c)) larger hc
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.AliasProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.AliasProof
