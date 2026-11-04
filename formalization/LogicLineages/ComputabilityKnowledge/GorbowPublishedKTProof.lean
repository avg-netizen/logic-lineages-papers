module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedRevisionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventualProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! Finite KT and KT+UBF proofs on the actual published-D presentation. Every
explicit axiom is true at every actual positive stage by R014--R017 and the
trivial veracity semantics. Finite mixed proofs are sound with their explicit
recursive threshold, uniformly over valuations: ordinary blocks use the existing
theory soundness, and the three closed theorem rules reuse the paid sorted
revision rule thresholds on the same actual ground and theorem codes. No original
Base correspondence, internal HB2/HB3/Lob or source12 promotion is claimed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB GorbowPublishedModel

/-! ### Axioms at actual positive stages -/

private theorem veracityTrue (pF pR : Program 1) (q : Program 5) (c : Code) (k : Nat) :
    GorbowSortedKnowledgeAxioms.veracity.realize
      (GorbowPublishedRevision.stage pF pR q c k) Fin.elim0 := by
  intro a _ x _ hk
  exact And.right hk

theorem axiomSoundness : GorbowPublishedKT.Targets.AxiomSoundness := by
  intro pF pR q c hA withUBF sigma hax k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  cases hax with
  | d sigma hd =>
    exact GorbowPublishedRevision.Proof.stageAxioms pF pR q c hA (j+1) sigma hd
  | negation =>
    exact (GorbowPublishedBooleanTruth.Proof.positiveBooleanAxioms pF pR q c hA j).1
  | implication =>
    exact (GorbowPublishedBooleanTruth.Proof.positiveBooleanAxioms pF pR q c hA j).2.1
  | conjunction =>
    exact (GorbowPublishedBooleanTruth.Proof.positiveBooleanAxioms pF pR q c hA j).2.2.1
  | disjunction =>
    exact (GorbowPublishedBooleanTruth.Proof.positiveBooleanAxioms pF pR q c hA j).2.2.2
  | universal =>
    exact (GorbowPublishedQuantifierTruth.Proof.positiveQuantifierAxioms pF pR q c hA j).1
  | existential =>
    exact (GorbowPublishedQuantifierTruth.Proof.positiveQuantifierAxioms pF pR q c hA j).2.1
  | atomic R names hr hn hc =>
    exact GorbowPublishedAtomicTruth.Proof.positiveAtomicSchemas pF pR q c hA _ _ R names
      hr hn hc j
  | veracity => exact veracityTrue pF pR q c (j+1)
  | barcan _ =>
    exact (GorbowPublishedQuantifierTruth.Proof.positiveQuantifierAxioms pF pR q c hA j).2.2

/-! ### Rule steps on uniform thresholds -/

private theorem ordinarySound (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (withUBF : Bool) {n : Nat} {phi : Formula n}
    (d : GorbowTheoryProof.Derivation (GorbowPublishedKT.Axiom withUBF pF pR q c) phi) :
    UniformThreshold pF pR q c phi 1 := by
  intro k hk env
  exact GorbowTheoryProofProof.theorySoundness (GorbowPublishedKT.Axiom withUBF pF pR q c) n phi d
    (GorbowPublishedRevision.stage pF pR q c k)
    (fun sigma hs => axiomSoundness pF pR q c hA withUBF sigma hs k hk) env

private theorem mpSound {pF pR : Program 1} {q : Program 5} {c : Code} {n : Nat}
    {a b : Formula n} {N M : Nat} (hab : UniformThreshold pF pR q c (.imp a b) N)
    (ha : UniformThreshold pF pR q c a M) : UniformThreshold pF pR q c b (max N M) := by
  intro k hk env
  exact hab k (le_trans (le_max_left N M) hk) env (ha k (le_trans (le_max_right N M) hk) env)

private theorem generalizeSound {pF pR : Program 1} {q : Program 5} {c : Code} {n : Nat}
    {a : Formula (n+1)} {N : Nat} (h : UniformThreshold pF pR q c a N) :
    UniformThreshold pF pR q c (.all a) N := by
  intro k hk env x
  exact h k hk (Fin.cases x env)

private theorem closedThreshold (pF pR : Program 1) (q : Program 5) (c : Code)
    (sigma : Sentence) (N : Nat) :
    UniformThreshold pF pR q c sigma N ↔
      GorbowSortedRevisionEventual.Threshold (ground pF pR q) (theoremCodes pF pR q c) sigma N := by
  constructor
  · intro h k hk
    exact h k hk Fin.elim0
  · intro h k hk env
    have he : env = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [he]
    exact h k hk

private theorem introSound {pF pR : Program 1} {q : Program 5} {c : Code} {sigma : Sentence}
    {N : Nat} (h : UniformThreshold pF pR q c sigma N) :
    UniformThreshold pF pR q c (GorbowSortedRevision.truthSentence sigma) (N+1) :=
  (closedThreshold pF pR q c (GorbowSortedRevision.truthSentence sigma) (N+1)).mpr
    ((GorbowSortedRevisionEventualProof.ruleThresholds (ground pF pR q) (theoremCodes pF pR q c)
      sigma N).1 ((closedThreshold pF pR q c sigma N).mp h))

private theorem elimSound {pF pR : Program 1} {q : Program 5} {c : Code} {sigma : Sentence}
    {N : Nat} (h : UniformThreshold pF pR q c (GorbowSortedRevision.truthSentence sigma) N) :
    UniformThreshold pF pR q c sigma N :=
  (closedThreshold pF pR q c sigma N).mpr
    ((GorbowSortedRevisionEventualProof.ruleThresholds (ground pF pR q) (theoremCodes pF pR q c)
      sigma N).2.1 ((closedThreshold pF pR q c (GorbowSortedRevision.truthSentence sigma) N).mp h))

private theorem necSound {pF pR : Program 1} {q : Program 5} {c : Code} {sigma : Sentence}
    {N : Nat} (h : UniformThreshold pF pR q c sigma N) :
    UniformThreshold pF pR q c (GorbowSortedRevisionEventual.allAgentsKnow sigma) (N+1) :=
  (closedThreshold pF pR q c (GorbowSortedRevisionEventual.allAgentsKnow sigma) (N+1)).mpr
    ((GorbowSortedRevisionEventualProof.ruleThresholds (ground pF pR q) (theoremCodes pF pR q c)
      sigma N).2.2 ((closedThreshold pF pR q c sigma N).mp h))

/-! ### Finite proof soundness and consistency -/

theorem uniformProofSoundness : GorbowPublishedKT.Targets.UniformProofSoundness := by
  intro pF pR q c hA withUBF n phi p
  induction p with
  | ordinary d => exact ordinarySound pF pR q c hA withUBF d
  | mp p r ihp ihr => exact mpSound ihp ihr
  | generalize p ih => exact generalizeSound ih
  | truthIntroduction p ih => exact introSound ih
  | truthElimination p ih => exact elimSound ih
  | knowledgeNecessitation p ih => exact necSound ih

theorem eventualTheorems : GorbowPublishedKT.Targets.EventualTheorems := by
  intro pF pR q c hA withUBF sigma hp
  obtain ⟨p⟩ := hp
  exact ⟨threshold p, (closedThreshold pF pR q c sigma (threshold p)).mp
    (uniformProofSoundness pF pR q c hA withUBF 0 sigma p)⟩

theorem consistency : GorbowPublishedKT.Targets.Consistency := by
  intro pF pR q c hA withUBF hp
  obtain ⟨p⟩ := hp
  exact falseEquality_not_realized (GorbowPublishedRevision.stage pF pR q c (threshold p))
    (uniformProofSoundness pF pR q c hA withUBF 0 falseEquality p (threshold p) (le_refl _)
      Fin.elim0)

theorem concretePair : GorbowPublishedKT.Targets.ConcretePair := by
  obtain ⟨pF, pR, q, c, hA⟩ := GorbowPublishedDCB.Proof.actualParameters
  exact ⟨pF, pR, q, c, hA, consistency pF pR q c hA false, consistency pF pR q c hA true⟩

theorem fullTarget : GorbowPublishedKT.Targets.Target :=
  ⟨axiomSoundness, uniformProofSoundness, eventualTheorems, consistency, concretePair⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.Proof
