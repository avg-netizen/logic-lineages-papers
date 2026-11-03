module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- An unconditional actual syntactic diagonal inside each actual D. -/
def ActualDiagonal : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ theta : Sentence,
  Nonempty (Derivation (D pF pR q c) (GorbowBooleanTruth.biconditional
    (delta pF c theta) (.imp (prD pF c (delta pF c theta)) theta)))

/-- Only the displayed THREE internal HB instances are assumed. The existing
actual D-proof certification must supply all external necessitation steps. -/
def LocalLobReduction : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ theta : Sentence,
  Nonempty (Derivation (D pF pR q c)
    (hb2 pF c (delta pF c theta) (.imp (prD pF c (delta pF c theta)) theta))) →
  Nonempty (Derivation (D pF pR q c)
    (hb2 pF c (prD pF c (delta pF c theta)) theta)) →
  Nonempty (Derivation (D pF pR q c) (hb3 pF c (delta pF c theta))) →
  Nonempty (Derivation (D pF pR q c) (.imp (prD pF c theta) theta)) →
  Nonempty (Derivation (D pF pR q c) theta)

/-- A genuine proof of the Lob rule once the real internal HB2/HB3 obligations
are discharged for this D. This conditional theorem does not discharge them. -/
def GlobalLobReduction : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  (∀ sigma tau : Sentence,
    Nonempty (Derivation (D pF pR q c) (hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c) (hb3 pF c sigma))) →
  ∀ theta : Sentence,
  Nonempty (Derivation (D pF pR q c) (.imp (prD pF c theta) theta)) →
  Nonempty (Derivation (D pF pR q c) theta)

def Target : Prop := ActualDiagonal ∧ LocalLobReduction ∧ GlobalLobReduction

end LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.Targets
