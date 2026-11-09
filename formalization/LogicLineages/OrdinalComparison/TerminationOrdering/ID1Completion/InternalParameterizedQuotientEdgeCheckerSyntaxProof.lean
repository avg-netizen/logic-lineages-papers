module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedQuotientEdgeChecker
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem coreAcceptedRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (coreAccepted data oldStep x y certificate parameter).relabel j =
      coreAccepted data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  unfold coreAccepted
  rw [graph4Rename,sucRelabel,zRelabel]

theorem acceptedRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (accepted data oldStep x y certificate parameter).relabel j =
      accepted data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  unfold accepted
  rw [graph4Rename,sucRelabel,zRelabel]

theorem typedAcceptedRename {α β : Type} (data : Data)
    (value typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (typedAccepted data value typ parameter).relabel j =
      typedAccepted data (value.relabel j) (typ.relabel j) (parameter.relabel j) := by
  unfold typedAccepted
  rw [graph3Rename,sucRelabel,zRelabel]

theorem sourceRepresentativeGraphRename {α β : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (sourceRepresentativeGraph data out input parameter).relabel j =
      sourceRepresentativeGraph data (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  unfold sourceRepresentativeGraph
  rw [graph2Rename]

theorem targetRepresentativeGraphRename {α β : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (targetRepresentativeGraph data out input parameter).relabel j =
      targetRepresentativeGraph data (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  unfold targetRepresentativeGraph
  rw [graph2Rename]

theorem sourceTypeGraphRename {α β : Type}
    (typ value : OrdinaryArithmetic.Term α) (j : α → β) :
    (sourceTypeGraph typ value).relabel j =
      sourceTypeGraph (typ.relabel j) (value.relabel j) := by
  unfold sourceTypeGraph
  rw [graph1Rename]

theorem requirementsRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y s t k parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (requirements data oldStep x y s t k parameter).relabel j =
      requirements data oldStep (x.relabel j) (y.relabel j) (s.relabel j)
        (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  change (InternalOriginalUniformStepGuard.stepAccepted data oldStep s t k parameter).relabel j ⊓
    ((sourceRepresentativeGraph data x s parameter).relabel j ⊓
      (targetRepresentativeGraph data y t parameter).relabel j) = _
  unfold InternalOriginalUniformStepGuard.stepAccepted
  rw [graph4Rename,sucRelabel,zRelabel,
    sourceRepresentativeGraphRename,targetRepresentativeGraphRename]
  rfl

theorem normalizedRequirementsRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y s t k parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (normalizedRequirements data oldStep x y s t k parameter).relabel j =
      normalizedRequirements data oldStep (x.relabel j) (y.relabel j) (s.relabel j)
        (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  change (InternalOriginalUniformStepGuard.stepAccepted data oldStep s t k parameter).relabel j ⊓
    ((InternalParameterizedCanonicalResultFold.foldGraph data x s parameter).relabel j ⊓
      (InternalParameterizedCanonicalResultFold.foldGraph data y t parameter).relabel j) = _
  unfold InternalOriginalUniformStepGuard.stepAccepted
    InternalParameterizedCanonicalResultFold.foldGraph
  rw [graph4Rename,sucRelabel,zRelabel,graph2Rename,graph2Rename]
  rfl

theorem typedRequirementsRename {α β : Type} (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (typedRequirements data oldStep x y certificate typ parameter).relabel j =
      typedRequirements data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (typ.relabel j) (parameter.relabel j) := by
  change (coreAccepted data oldStep x y certificate parameter).relabel j ⊓
    ((typedAccepted data x typ parameter).relabel j ⊓
      (typedAccepted data y typ parameter).relabel j) = _
  rw [coreAcceptedRename,typedAcceptedRename,typedAcceptedRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
