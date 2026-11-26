module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseStatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.ConsumerProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
/-- Only source inclusion, no re-selection of pF/pR/c or CK. -/
theorem intoD (pF pR : Program 1) (q : Program 5) (c : Code) (sigma : Sentence)
 (h : Nonempty (Derivation (S pF pR q) sigma)) :
 Nonempty (Derivation (D pF pR q c) sigma) :=
 GorbowTheoryProofProof.monotonicity _ _ (fun _ hs => Or.inl hs) 0 sigma h

theorem consumers (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat)
 (hA : Actual pF pR q c) (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag)
 (h2 : ∀ sigma tau : Sentence, Nonempty (Derivation (S pF pR q)
  (GorbowPublishedLobReduction.hb2 pF c sigma tau)))
 (h3 : ∀ sigma : Sentence, Nonempty (Derivation (S pF pR q)
  (GorbowPublishedLobReduction.hb3 pF c sigma))) :
 (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
  (GorbowPublishedLobReduction.hb2 pF c sigma tau))) ∧
 (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
  (GorbowPublishedLobReduction.hb3 pF c sigma))) ∧
 (∀ theta : Sentence, Nonempty (Derivation (D pF pR q c) (.imp (prD pF c theta) theta)) →
  Nonempty (Derivation (D pF pR q c) theta)) ∧
 (∀ A : Selector, Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (sourceC tag A)
   (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))) := by
 have h2D := fun sigma tau => intoD pF pR q c _ (h2 sigma tau)
 have h3D := fun sigma => intoD pF pR q c _ (h3 sigma)
 refine ⟨h2D,h3D,GorbowPublishedLobReduction.StatementChecks.globalLobReduction pF pR q c hA h2D h3D,?_⟩
 intro A
 let d := GorbowPublishedLobReduction.delta pF c (collapseDelta tag A)
 exact CollapseStatementChecks.localReduction pF pR q c hA tag hFP A
  (h2D d (.imp (prD pF c d) (collapseDelta tag A)))
  (h2D (prD pF c d) (collapseDelta tag A)) (h3D d)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.ConsumerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.ConsumerProof
