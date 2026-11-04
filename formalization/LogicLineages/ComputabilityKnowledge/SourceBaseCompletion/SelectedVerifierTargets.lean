module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseTargets
public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions

@[expose] public section
/-! Frozen unpaid endpoints for the continuing source-collapse route.
These definitions are specifications, not additional axioms or paid theorems.
Internal HB is required for ONE certified presentation with its actual CK
program installed. Extensional standard-N verifier calibration alone is not
silently promoted to an internal universal program-correctness theorem. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.SelectedVerifierTargets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

def SelectedCertifiedPresentation : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb2 pF c sigma tau))) ∧
    (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb3 pF c sigma)))

/-- The missing actual ordinary-arithmetic recursion certificate, for the
entire original PR AST, including recursion. No U/u/program/checker atom or
semantic truth-to-proof principle is allowed in the graph. -/
def GuardedRecursionCertificates : Prop :=
  ∀ (T : Sentence → Prop) n (p : Program n) (inputs : List.Vector Nat n),
    Nonempty (Derivation T (GorbowOrdinaryArithmeticGraphs.closedGraph p inputs
      (evaluate p inputs)))

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.SelectedVerifierTargets
