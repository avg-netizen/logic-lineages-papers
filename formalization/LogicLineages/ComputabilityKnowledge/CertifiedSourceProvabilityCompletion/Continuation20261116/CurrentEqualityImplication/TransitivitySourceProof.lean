module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowPublishedDCB
theorem exactTransitivityUnder : Targets.InternalTransitivityUnder := by
 intro installed lhs rhs k t old a baseX pF pR I ctx G P left middle right htu huv index fuel
 dsimp only
 intro hP hl hm hr htuCore huvCore
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := I.previous.current
 let V := RawReflexivityDispatcher.valid (ctx := ctx) J.vtag
 let FP := UniformClosedPropositional.formulaValid I.currentK.fval P
 let H1 := core I.currentK.coreTag index fuel (impValue J.ctag J.atag P (equalValue J.ctag J.atag left middle)) htu
 let H2 := core I.currentK.coreTag index fuel (impValue J.ctag J.atag P (equalValue J.ctag J.atag middle right)) huv
 let Gamma := [FP,V left,V middle,V right,H1,H2]
 have hlocal (phi : Formula ctx) (h : phi ∈ Gamma) : Nonempty (Hilbert.Local T ctx Gamma phi) := ⟨.hypothesis h⟩
 have hout := TransitivityInternalProof.internal p installed lhs rhs t old a _ I Gamma P left middle right htu huv index fuel
  (hlocal FP (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inl rfl))
  (hlocal (V left) (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inr (Or.inl rfl)))
  (hlocal (V middle) (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inr (Or.inr (Or.inl rfl))))
  (hlocal (V right) (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  (hlocal H1 (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  (hlocal H2 (by simp only [Gamma,List.mem_cons,List.mem_singleton]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  simp only [Gamma,List.mem_cons,List.mem_singleton] at hmem
  rcases hmem with he | he | he | he | he | he
  · subst psi; exact hP
  · subst psi; exact hl
  · subst psi; exact hm
  · subst psi; exact hr
  · subst psi; exact htuCore
  · subst psi; exact huvCore
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX) hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
