module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every raw head/Context input, including both decoder failures and n = 0.
Native calibration is not used as an internal inference rule. -/
def NativeOriginalWindow : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  OriginalUniverseDecoder.HeadWindowCalibrated n arity (window n arity)

/-- Actual raw source-head membership plus actual original head validity.
This is not yet the encoded-head-list predicate used by Fields. -/
def sourceHead {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (head symbols types : OTerm alpha) : Formula alpha :=
  graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
    graph3 (Continuation20261114.OriginalSourceHeads.member n arity) (numeral 1) head symbols types

/-- The original ordinary universe admission supplies the head-window test.
ArrowClosed is the explicit original subtype closure condition, not a property
of decoded Context. No supplied head success, validity, image or H calibration. -/
def InternalOrdinaryHead : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw head base typ gamma context symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)) →
  Nonempty (Derivation body Delta
    (TermAccepted H (OriginalUniverseDomainCoverage.member n) (window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 contextSymbols symbols context)) →
  Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) →
  Nonempty (Derivation body Delta (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta (sourceHead n arity head symbols types))

/-- The original numbered universe admission supplies the head-window test.
ArrowClosed is the explicit original subtype closure condition, not a property
of decoded Context. No supplied head success, validity, image or H calibration. -/
def InternalNumberedHead : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw label head recorded base extraTypes extra typ gamma context symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,recorded,base,extraTypes,extra])) →
  Nonempty (Derivation body Delta
    (TermAccepted H (OriginalUniverseDomainCoverage.member n) (window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 contextSymbols symbols context)) →
  Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) →
  Nonempty (Derivation body Delta (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta (sourceHead n arity head symbols types))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
