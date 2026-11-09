module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformVertexPath
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem vertexInputsRename {α β : Type} (p d e a x : OTerm α) (j : α → β) :
    (fun i => (InternalApplicationPathMap.vertexArguments p d e a x i).relabel j) =
      InternalApplicationPathMap.vertexArguments (p.relabel j) (d.relabel j)
        (e.relabel j) (a.relabel j) (x.relabel j) := by
  simp only [InternalApplicationPathMap.vertexArguments,consTermRename,emptyRename]

@[simp] theorem invariantRename {α β : Type} (data : Data) (p d e a x : OTerm α) (j : α → β) :
    (invariantAccepted data p d e a x).relabel j =
      invariantAccepted data (p.relabel j) (d.relabel j) (e.relabel j) (a.relabel j) (x.relabel j) := by
  simp only [invariantAccepted,programRename,vertexInputsRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem vertexRename {α β : Type} (data : Data) (oldVertex : Program 5)
    (out p d e a x : OTerm α) (j : α → β) :
    (vertexGraph data oldVertex out p d e a x).relabel j =
      vertexGraph data oldVertex (out.relabel j) (p.relabel j) (d.relabel j)
        (e.relabel j) (a.relabel j) (x.relabel j) := by
  simp only [vertexGraph,programRename,vertexInputsRename]

@[simp] theorem edgeAcceptedRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) (j : α → β) :
    (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate parameter).relabel j =
      InternalParameterizedQuotientEdgeChecker.accepted data oldStep (x.relabel j)
        (y.relabel j) (certificate.relabel j) (parameter.relabel j) := by
  simp only [InternalParameterizedQuotientEdgeChecker.accepted,graph4Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSyntaxProof
