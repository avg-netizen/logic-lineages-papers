module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedPathChecker InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalPathCheckerSyntaxProof (tripleRename pairGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem quadrupleRename {α β : Type} (a b c d : OTerm α) (j : α → β) :
    (fun i => (quadruple a b c d i).relabel j) =
      quadruple (a.relabel j) (b.relabel j) (c.relabel j) (d.relabel j) := by
  simp only [quadruple,consTermRename,emptyRename]

@[simp] theorem edgeRename {α β : Type}
    (edge : Program 4)
    (x y certificate parameter : OTerm α) (j : α → β) :
    (edgeGraph edge x y certificate parameter).relabel j =
      edgeGraph edge (x.relabel j) (y.relabel j) (certificate.relabel j) (parameter.relabel j) := by
  simp only [edgeGraph,programRename,sucRelabel,zRelabel,quadrupleRename]

@[simp] theorem summaryRename {α β : Type}
    (edge : Program 4)
    (out code target parameter : OTerm α) (j : α → β) :
    (summaryGraph edge out code target parameter).relabel j =
      summaryGraph edge (out.relabel j) (code.relabel j) (target.relabel j) (parameter.relabel j) := by
  simp only [summaryGraph,programRename,tripleRename]

@[simp] theorem finishRename {α β : Type}
    (edge : Program 4) (positive : Bool)
    (out x y state parameter : OTerm α) (j : α → β) :
    (finishGraph edge positive out x y state parameter).relabel j =
      finishGraph edge positive (out.relabel j) (x.relabel j) (y.relabel j) (state.relabel j) (parameter.relabel j) := by
  simp only [finishGraph,programRename,quadrupleRename]

@[simp] theorem checkerRename {α β : Type}
    (edge : Program 4) (positive : Bool)
    (out x y code parameter : OTerm α) (j : α → β) :
    (checkerGraph edge positive out x y code parameter).relabel j =
      checkerGraph edge positive (out.relabel j) (x.relabel j) (y.relabel j) (code.relabel j) (parameter.relabel j) := by
  simp only [checkerGraph,programRename,quadrupleRename]

@[simp] theorem pathRename {α β : Type}
    (edge : Program 4)
    (x y code parameter : OTerm α) (j : α → β) :
    (pathGraph edge x y code parameter).relabel j =
      pathGraph edge (x.relabel j) (y.relabel j) (code.relabel j) (parameter.relabel j) := by
  simp only [pathGraph,checkerRename,sucRelabel,zRelabel]

@[simp] theorem positiveRename {α β : Type}
    (edge : Program 4)
    (x y code parameter : OTerm α) (j : α → β) :
    (positiveGraph edge x y code parameter).relabel j =
      positiveGraph edge (x.relabel j) (y.relabel j) (code.relabel j) (parameter.relabel j) := by
  simp only [positiveGraph,checkerRename,sucRelabel,zRelabel]

@[simp] theorem consPremisesRename {α β : Type}
    (code raw tail vertex certificate : OTerm α) (j : α → β) :
    (consPremises code raw tail vertex certificate).relabel j =
      consPremises (code.relabel j) (raw.relabel j) (tail.relabel j)
        (vertex.relabel j) (certificate.relabel j) :=
  InternalPathCheckerSyntaxProof.consPremisesRename code raw tail vertex certificate j

def checkerConsResult {α : Type} (edge : Program 4) (positive : Bool)
    (x y code tail vertex certificate parameter : OTerm α) : Formula α :=
  (checkerGraph edge positive (suc z) x y code parameter).iff
    (edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter)

@[simp] theorem checkerConsResultRename {α β : Type} (edge : Program 4) (positive : Bool)
    (x y code tail vertex certificate parameter : OTerm α) (j : α → β) :
    (checkerConsResult edge positive x y code tail vertex certificate parameter).relabel j =
      checkerConsResult edge positive (x.relabel j) (y.relabel j) (code.relabel j)
        (tail.relabel j) (vertex.relabel j) (certificate.relabel j) (parameter.relabel j) := by
  change ((checkerGraph edge positive (suc z) x y code parameter).relabel j).iff
    ((edgeGraph edge x vertex certificate parameter).relabel j ⊓
      (pathGraph edge vertex y tail parameter).relabel j) = _
  simp only [checkerRename,sucRelabel,zRelabel,edgeRename,pathRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof

