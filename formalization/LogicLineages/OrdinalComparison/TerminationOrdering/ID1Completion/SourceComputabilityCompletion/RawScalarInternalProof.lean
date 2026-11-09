module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection
open InternalOriginalUniformDescentSelectionInternalProof (typedRecover)
open InternalApplicationStepPeelSupportProof (andLeft andRight sameAccept)
open InternalAcceptanceConjunctionProof InternalControlGraphSupportProof
open SourceComputabilityCompletion.RawScalar

theorem typedScalar {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}
    (data : Data) (value typ parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Delta
      (typedAccepted data.oldRepresentative (validity data) data.member value typ parameter))) :
    Nonempty (Derivation body Delta (accepted data value parameter)) := by
  have hf := typedRecover data.oldRepresentative (validity data) data.member value typ parameter h
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![value,parameter]
  exact conjunctionAccept (validity data) (fixed data) xs
    (andLeft (andRight hf))
    (sameAccept
      (InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative (validity data))
      (.projection 0) value xs (andRight (andRight (andRight hf))) (projectionValue 0 xs))

theorem actualParameterizedTypedScalar : RawScalarTargets.ActualParameterizedTypedScalar := by
  intro body data α Delta value typ parameter
  let P := typedAccepted data.oldRepresentative (validity data) data.member value typ parameter
  obtain ⟨d⟩ := typedScalar (body := body) (Delta := P :: Delta) data value typ parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarInternalProof
