module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTagSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.KnownProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

open OriginalTypedDecoderStepSpecification
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorValue bottomConstructorValue)
open OriginalUniverseDecoderTransportRejectedProof

theorem termKnown (n : Nat) (arity : Fin n → Nat) (H : Program 1) (i : Fin 8)
    (raw payload : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have ha := ObservationPartsProof.admission n arity H false raw xs ho
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact LeafProof.variableCode n arity H raw payload xs (variableConstructorValue raw payload hp) ho
  · intro ht hp
    exact UnaryTagsProof.lambda n arity H raw xs ht ho ih
  · intro ht hp
    exact BinaryTagsProof.application n arity H raw xs ht ho ih
  · intro ht hp
    exact LeafProof.bottom n arity H raw payload xs (bottomConstructorValue raw payload hp) ho
  · intro ht hp
    exact UnaryTagsProof.ordinary n arity H raw xs ht ho ih
  · intro ht hp
    exact NumberedTagProof.numbered n arity H raw xs ht ho ih
  · intro ht hp
    exact termSix H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact termSeven H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      raw payload (xs 5) (xs 6) (xs 2) _ hp ha

theorem argumentsKnown (n : Nat) (arity : Fin n → Nat) (H : Program 1) (i : Fin 8)
    (raw payload : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (result n true raw xs)) := by
  have ha := ObservationPartsProof.admission n arity H true raw xs ho
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      0 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      1 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      2 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      3 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      4 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact argumentsOther H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      5 (by decide) (by decide) raw payload (xs 5) (xs 6) (xs 2) _ hp ha
  · intro ht hp
    exact LeafProof.nilCode n arity H raw xs
      (OriginalUniverseDecoderTransportTagSupportProof.acceptedNilConstructor H (OriginalUniverseDomainCoverage.member n)
        (OriginalGuardedHeadSourceCoverage.window n arity) raw payload (xs 5) (xs 6) (xs 2) hp ha) ho
  · intro ht hp
    exact BinaryTagsProof.cons n arity H raw xs ht ho ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.KnownProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.KnownProof
