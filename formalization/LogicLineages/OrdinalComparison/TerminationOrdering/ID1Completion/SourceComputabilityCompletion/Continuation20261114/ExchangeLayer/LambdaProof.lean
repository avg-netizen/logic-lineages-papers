module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.LambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
abbrev OT := InternalGraphComposition.OTerm

open InternalSupportProof

theorem internalLambda : Targets.InternalLambda := by
  intro body alpha Delta xs hx hy
  have hs := sameTag xs 1 hx hy
  have hc := chooseAccept (eqField 0 7) dispatch (InternalAcceptance.constantZero 19) xs hs
  have ht := chooseNumeral 1 1 lambdaCase afterLambda xs hx
  simp only [ite_true] at ht
  constructor
  · intro h
    obtain ⟨hh⟩ := bothRecover (eqField 1 8) (.projection 14) xs (ht.mp (hc.mp h))
    obtain ⟨he⟩ := eqRecover 1 8 xs ⟨Derivation.conjunctionLeft hh⟩
    obtain ⟨hl⟩ := projectionRecover 14 xs ⟨Derivation.conjunctionRight hh⟩
    exact ⟨Derivation.conjunctionIntroduction he hl⟩
  · rintro ⟨h⟩
    apply hc.mpr
    apply ht.mpr
    exact bothAccept (eqField 1 8) (.projection 14) xs
      (eqAccept 1 8 xs ⟨Derivation.conjunctionLeft h⟩)
      (projectionAt 14 xs (suc z) ⟨Derivation.conjunctionRight h⟩)

theorem internalTagMismatch : Targets.InternalTagMismatch := by
  intro body alpha Delta xs hn
  let A := programGraph layer (suc z) xs
  have hn' := withHyp hn A
  have he : Nonempty (Derivation body (A :: Delta) (equal (xs 0) (xs 7)).not) := by
    simpa only [equalEqn] using hn'
  have hz := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    (.projection 0) (.projection 7) (xs 0) (xs 7) xs
    (projectionValue 0 xs) (projectionValue 7 xs) he
  have hbad := zeroBranchElim (eqField 0 7) (InternalAcceptance.constantZero 19) dispatch (suc z) xs hz
    (show Nonempty (Derivation body (A :: Delta) (programGraph layer (suc z) xs)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hu⟩ := valueUnique (InternalAcceptance.constantZero 19) (suc z) z xs hbad (constantZeroValue xs)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hu)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.LambdaProof
