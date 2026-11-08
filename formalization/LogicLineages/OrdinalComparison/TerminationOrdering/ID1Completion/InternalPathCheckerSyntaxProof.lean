module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalPathChecker InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof

@[simp] theorem tripleRename {α β : Type} (a b c : OTerm α) (j : α → β) :
    (fun i => (triple a b c i).relabel j) = triple (a.relabel j) (b.relabel j) (c.relabel j) := by
  simp only [triple,consTermRename,emptyRename]

@[simp] theorem pairGraphRename {α β : Type} (raw vertex certificate : OTerm α) (j : α → β) :
    (pairGraph raw vertex certificate).relabel j =
      pairGraph (raw.relabel j) (vertex.relabel j) (certificate.relabel j) := by
  simp only [pairGraph,programRename,consTermRename,emptyRename]

@[simp] theorem edgeRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3)
    (x y certificate : OTerm α) (j : α → β) :
    (edgeGraph edge x y certificate).relabel j =
      edgeGraph edge (x.relabel j) (y.relabel j) (certificate.relabel j) := by
  simp only [edgeGraph,programRename,sucRelabel,zRelabel,tripleRename]

@[simp] theorem summaryRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3)
    (out code target : OTerm α) (j : α → β) :
    (summaryGraph edge out code target).relabel j =
      summaryGraph edge (out.relabel j) (code.relabel j) (target.relabel j) := by
  simp only [summaryGraph,programRename,consTermRename,emptyRename]

@[simp] theorem finishRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3) (positive : Bool)
    (out x y state : OTerm α) (j : α → β) :
    (finishGraph edge positive out x y state).relabel j =
      finishGraph edge positive (out.relabel j) (x.relabel j) (y.relabel j) (state.relabel j) := by
  simp only [finishGraph,programRename,tripleRename]

@[simp] theorem checkerRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3) (positive : Bool)
    (out x y code : OTerm α) (j : α → β) :
    (checkerGraph edge positive out x y code).relabel j =
      checkerGraph edge positive (out.relabel j) (x.relabel j) (y.relabel j) (code.relabel j) := by
  simp only [checkerGraph,programRename,tripleRename]

@[simp] theorem pathRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3)
    (x y code : OTerm α) (j : α → β) :
    (pathGraph edge x y code).relabel j =
      pathGraph edge (x.relabel j) (y.relabel j) (code.relabel j) := by
  simp only [pathGraph,checkerRename,sucRelabel,zRelabel]

@[simp] theorem positiveRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3)
    (x y code : OTerm α) (j : α → β) :
    (positiveGraph edge x y code).relabel j =
      positiveGraph edge (x.relabel j) (y.relabel j) (code.relabel j) := by
  simp only [positiveGraph,checkerRename,sucRelabel,zRelabel]

@[simp] theorem consPremisesRename {α β : Type}
    (code raw tail vertex certificate : OTerm α) (j : α → β) :
    (consPremises code raw tail vertex certificate).relabel j =
      consPremises (code.relabel j) (raw.relabel j) (tail.relabel j)
        (vertex.relabel j) (certificate.relabel j) := by
  change (pairGraph raw vertex certificate).relabel j ⊓
    (consGraph code raw tail).relabel j = _
  rw [pairGraphRename,consGraphRename]
  rfl

def checkerConsResult {α : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3) (positive : Bool)
    (x y code tail vertex certificate : OTerm α) : Formula α :=
  (checkerGraph edge positive (suc z) x y code).iff
    (edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail)

@[simp] theorem checkerConsResultRename {α β : Type}
    (edge : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3) (positive : Bool)
    (x y code tail vertex certificate : OTerm α) (j : α → β) :
    (checkerConsResult edge positive x y code tail vertex certificate).relabel j =
      checkerConsResult edge positive (x.relabel j) (y.relabel j) (code.relabel j)
        (tail.relabel j) (vertex.relabel j) (certificate.relabel j) := by
  change ((checkerGraph edge positive (suc z) x y code).relabel j).iff
    ((edgeGraph edge x vertex certificate).relabel j ⊓
      (pathGraph edge vertex y tail).relabel j) = _
  simp only [checkerRename,sucRelabel,zRelabel,edgeRename,pathRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
