module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedQuotientEdgeChecker
open InternalParameterizedQuotientEdgeCheckerSupportProof InternalParameterizedQuotientEdgeCheckerNormalizedProof
open InternalParameterizedQuotientEdgeCheckerTypedProof InternalParameterizedQuotientEdgeCheckerTargets
open InternalParameterizedApplicationStepCheckerSyntaxProof (guardedIffAt)
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)

theorem actualParameterizedQuotientAcceptance : ActualParameterizedQuotientAcceptance := by
  intro body data oldStep α Delta x y certificate s t k parameter
  apply guardedIffAt
  · exact coreRecover data oldStep x y certificate s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact coreAccept data oldStep x y certificate s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualParameterizedNormalizedQuotientAcceptance :
    ActualParameterizedNormalizedQuotientAcceptance := by
  intro body data oldStep α Delta x y certificate s t k parameter
  apply guardedIffAt
  · exact normalizedRecover data oldStep x y certificate s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact normalizedAccept data oldStep x y certificate s t k parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualParameterizedTypedQuotientAcceptance : ActualParameterizedTypedQuotientAcceptance := by
  intro body data oldStep α Delta x y certificate typ parameter
  apply guardedIffAt
  · exact wrapperRecover data oldStep x y certificate typ parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact wrapperAccept data oldStep x y certificate typ parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualParameterizedTypedQuotientPropagation : ActualParameterizedTypedQuotientPropagation := by
  intro body data oldStep α Delta x y certificate typ parameter
  let P := typedAccepted data x typ parameter ⊓ accepted data oldStep x y certificate parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := typedPropagation data oldStep x y certificate typ parameter (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerProof
