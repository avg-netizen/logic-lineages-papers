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
  (hlocal FP List.mem_cons_self)
  (hlocal (V left) (List.mem_cons_of_mem _ List.mem_cons_self))
  (hlocal (V middle) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  (hlocal (V right) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  (hlocal H1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  (hlocal H2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hP
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hl
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hm
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hr
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact htuCore
  have he := List.mem_singleton.mp hmem
  subst psi
  exact huvCore
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX) hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
