module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.CodingProof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof GorbowFormulaSubstitution
open GorbowSortedSyntaxCode

theorem instantiateProv (pF : Program 1) (c : Code) (t : Term 0) :
 GorbowStandardInstances.instantiate (provability pF c) t = applyProv pF c t := by
 have he : (Fin.cases t Term.var : Fin 1 → Term 0) = (fun _ : Fin 1 => t) := by
  funext i
  exact Fin.eq_zero i ▸ rfl
 unfold GorbowStandardInstances.instantiate applyProv
 exact congrArg (fun s : Fin 1 → Term 0 => substituteFormula s (provability pF c)) he

/-- Only fixed external sentence codes are transported; this is the existing
literal coding derivation in the SAME S, not a universal syntax oracle. -/
theorem literalPrD (pF pR : Program 1) (q : Program 5) (c : Code)
 (hA : Actual pF pR q c) (sigma : Sentence) :
 Nonempty (Derivation (n := 0) (S pF pR q)
  (.conj
   (.imp (prD pF c sigma) (applyProv pF c (Term.numeral (formulaCode (.imp (rho pF c) sigma)))))
   (.imp (applyProv pF c (Term.numeral (formulaCode (.imp (rho pF c) sigma)))) (prD pF c sigma)))) := by
 have hCal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
 obtain ⟨hcoding⟩ := (GorbowSelectedDistribution.Proof.literalCodingCertificates
  (augmented pF q) pR hCal).2 (rho pF c) sigma
 have inclusion : ∀ tau, GorbowSelectedDistribution.Theory (augmented pF q) pR tau → S pF pR q tau := by
  intro tau ht
  rcases ht with hnamed | hdistribution
  · exact List.mem_append_left _ hnamed
  · subst tau
    exact List.mem_append_right _ (by simp)
 obtain ⟨hcodingS⟩ := GorbowTheoryProofProof.monotonicity _ _ inclusion 0 _ ⟨hcoding⟩
 obtain ⟨heq⟩ := GorbowTheoryEqualityProof.formulaEquivalence (S pF pR q) (provability pF c) _ _ hcodingS
 simpa only [instantiateProv,prD,GorbowBooleanTruth.biconditional] using (show Nonempty (Derivation (n := 0) (S pF pR q) _) from ⟨heq⟩)

def distribution (rho sigma tau : Sentence) : Sentence :=
 .imp (.imp rho (.imp sigma tau)) (.imp (.imp rho sigma) (.imp rho tau))

/-- Constructive certification of one finite external S-scheme proof, for
each external triple. Runtime witness parameters are not reflected from native
semantics into an internal universal theorem. -/
theorem certifiedDistribution (pF pR : Program 1) (q : Program 5) (c : Code)
 (hA : Actual pF pR q c) (sigma tau : Sentence) :
 Nonempty (Derivation (n := 0) (S pF pR q)
  (applyProv pF c (Term.numeral (formulaCode (distribution (rho pF c) sigma tau))))) :=
 GorbowPublishedDCB.Proof.sProofCertification pF pR q c hA _
  ⟨.logical (.s (rho pF c) sigma tau)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.CodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.CodingProof
