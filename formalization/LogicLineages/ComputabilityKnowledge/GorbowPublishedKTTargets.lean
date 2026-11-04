module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB GorbowPublishedModel

/-- ALL explicit KT and optional-UBF axioms true at every actual positive stage. -/
def AxiomSoundness : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ withUBF (sigma : Sentence), Axiom withUBF pF pR q c sigma →
  ∀ k, 1 ≤ k → sigma.realize (GorbowPublishedRevision.stage pF pR q c k) Fin.elim0

/-- GENUINE mutual use of ordinary Hilbert blocks and exactly the three closed
source rules: a proved explicit finite threshold, uniformly over all open valuations. -/
def UniformProofSoundness : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ withUBF n (phi : Formula n) (p : Proof withUBF pF pR q c phi),
    UniformThreshold pF pR q c phi (threshold p)

/-- Each actual closed theorem is eventually true on the SAME actual revisions. -/
def EventualTheorems : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ withUBF (sigma : Sentence), Nonempty (Proof withUBF pF pR q c sigma) →
    GorbowSortedRevisionEventual.Eventually (ground pF pR q) (theoremCodes pF pR q c) sigma

/-- No actual finite proof of the literal arithmetic falsehood, both optional theories. -/
def Consistency : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ withUBF, ¬ Nonempty (Proof withUBF pF pR q c GorbowSyntax.falseEquality)

/-- Actual simultaneous parameter choice and consistency of KT and KT+UBF;
no initial consistency/model assumption or original-Base identity is supplied. -/
def ConcretePair : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c ∧
    (¬ Nonempty (Proof false pF pR q c GorbowSyntax.falseEquality)) ∧
    (¬ Nonempty (Proof true pF pR q c GorbowSyntax.falseEquality))

def Target : Prop := AxiomSoundness ∧ UniformProofSoundness ∧ EventualTheorems ∧
  Consistency ∧ ConcretePair
end LogicLineages.ComputabilityKnowledge.GorbowPublishedKT.Targets
