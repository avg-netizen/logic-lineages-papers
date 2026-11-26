module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.AlignmentProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- The original closed named-coding theorem is embedded in the SAME S. -/
theorem sourceInclusion (pF pR : Program 1) (q : Program 5) :
 ∀ sigma, GorbowSelectedDistribution.Theory (augmented pF q) pR sigma → S pF pR q sigma := by
 intro sigma h
 rcases h with h | h
 · exact List.mem_append.mpr (Or.inl h)
 · subst h
   exact List.mem_append.mpr (Or.inr (by simp))

theorem outputAlignment (pF pR : Program 1) (q : Program 5) (c : Code)
 (hA : Actual pF pR q c) (sigma : Sentence) :
 Nonempty (Derivation (S pF pR q)
  (.equal (LiteralCheckerSuccessBridge.value (ctx := 0) pF c (prD pF c sigma))
   (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))))) := by
 have hcal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
 obtain ⟨hcode⟩ := (GorbowSelectedDistribution.Proof.literalCodingCertificates (augmented pF q) pR hcal).2
  (rho pF c) (prD pF c sigma)
 obtain ⟨hS⟩ := GorbowTheoryProofProof.monotonicity _ _ (sourceInclusion pF pR q) 0 _ ⟨hcode⟩
 let n := Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))
 obtain ⟨hadd⟩ := CurrentRecursionProducerCore.GuardBound.numeralAdd (ctx := 0) (S pF pR q) n n
 have he : GorbowSortedSyntaxCode.formulaCode (.imp (rho pF c) (prD pF c sigma)) = n+n := by
  simp only [GorbowSortedSyntaxCode.formulaCode,GorbowSortedSyntaxCode.tagFormula,GorbowCodeConstructors.formulaNumber,GorbowCodeConstructors.number,n,Nat.two_mul]
 unfold GorbowSelectedDistribution.implicationCode at hS
 rw [he] at hS
 exact ⟨Logic.trans _ _ _ hS (Support.equalitySymmetry _ _ hadd)⟩

theorem originalSyntax (pF : Program 1) (c : Code) (sigma : Sentence) :
 prD pF c sigma = .ex (.ex (CurrentPublishedProvabilityIntroduction.SyntaxSupport.checkerBody
  (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c)
  (CurrentPublishedProvabilityIntroduction.PublishedSyntax.argument pF c sigma))) :=
 CurrentPublishedProvabilityIntroduction.PublishedSyntax.applyProvShape pF c _

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.AlignmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.AlignmentProof
