module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TransformerCore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph
/-- Source-theory endpoint at the shared actual installation; no source
selection is performed here and no runtime certificate correctness is assumed. -/
theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX)
  f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar (SaturatedAxiomLeaf.saturated baseX))
 (N : LogicalInterface.Nodes (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX))
 (transformTag : Nat)
 (ht : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR (CurrentQuantifierLogicalSource.selectedOld rawOld) ar baseX))[transformTag]? = some ⟨3,program⟩) :
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 ∀ ctx (a w inputCode index fuel : Term ctx),
 let inst := call R.previous.previous.current.predTag (UniformClosedInstanceRecognizer.instanceCall R.previous.previous.current.itag a w ::ᵥ nil)
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (UniformClosedInstanceRecognizer.guards R.currentK.fval R.previous.previous.current.vtag a w)
   (.imp (accepted R.currentK.coreTag R.currentK.verifierTag index fuel inst inputCode)
    (accepted R.currentK.coreTag R.currentK.verifierTag index fuel
     (FixedFormulaSubstitution.unaryValue R.currentK.ctag 11 a)
     (call transformTag (a ::ᵥ w ::ᵥ inputCode ::ᵥ nil)))))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 dsimp only
 intro ctx a w inputCode index fuel
 let A := UniformClosedInstanceRecognizer.guards R.currentK.fval R.previous.previous.current.vtag a w
 let inst := call R.previous.previous.current.predTag (UniformClosedInstanceRecognizer.instanceCall R.previous.previous.current.itag a w ::ᵥ nil)
 let H := accepted R.currentK.coreTag R.currentK.verifierTag index fuel inst inputCode
 let G := [H,A]
 have hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G A := .hypothesis (by simp [G])
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G H := .hypothesis List.mem_cons_self
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨hout⟩ := TransformerCore.current p f lhs rhs t rawOld ar (SaturatedAxiomLeaf.saturated baseX) R N transformTag ht
  G a w inputCode index fuel hg hc
 exact GorbowTheoryProofProof.monotonicity _ _ (CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX)
  ctx _ ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.SourceEndpoint
