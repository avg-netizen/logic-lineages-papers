module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem typedAcceptedRename {α β : Type} (data : Data)
    (value typ parameter : OTerm α) (j : α → β) :
    (typedAccepted data value typ parameter).relabel j =
      typedAccepted data (value.relabel j) (typ.relabel j) (parameter.relabel j) :=
  InternalParameterizedQuotientEdgeCheckerSyntaxProof.typedAcceptedRename data value typ parameter j

@[simp] theorem edgeAcceptedRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) (j : α → β) :
    (edgeAccepted data oldStep x y certificate parameter).relabel j =
      edgeAccepted data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j) :=
  InternalParameterizedQuotientEdgeCheckerSyntaxProof.acceptedRename data oldStep x y certificate parameter j

@[simp] theorem applicationInputsRename {α β : Type} (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other parameter : OTerm α) (j : α → β) :
    (applicationInputs data oldStep arrow d e x y a certificate out other parameter).relabel j =
      applicationInputs data oldStep (arrow.relabel j) (d.relabel j) (e.relabel j)
        (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
        (out.relabel j) (other.relabel j) (parameter.relabel j) := by
  simp only [applicationInputs,conjunctionRename,typedAcceptedRename,edgeAcceptedRename,
    applicationGraph,InternalParameterizedCanonicalResultFoldSyntaxProof.applicationGraphRename]

@[simp] theorem corePremisesRename {α β : Type} (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other parameter : OTerm α) (j : α → β) :
    (corePremises data oldStep arrow d e x y a certificate out other parameter).relabel j =
      corePremises data oldStep (arrow.relabel j) (d.relabel j) (e.relabel j)
        (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
        (out.relabel j) (other.relabel j) (parameter.relabel j) := by
  simp only [corePremises,conjunctionRename,graph2Rename,applicationInputsRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
