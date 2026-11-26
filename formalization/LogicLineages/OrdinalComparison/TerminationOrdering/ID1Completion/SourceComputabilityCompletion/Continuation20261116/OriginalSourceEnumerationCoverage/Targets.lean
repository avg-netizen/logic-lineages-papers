module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
/-- Genuine source coverage of the literal enumeration frontend on the same
seed/parameter. All metadata and bounds are actual graph observations. The
original source size/label conditions compare this candidate with actual seed
bounds; no equality of candidates and seeds or WindowPrimary preservation is
asserted. Original Gamma length, parameter pairing, fuel and depth witnesses
must be derived internally. No assumed depth, Fields, code validity, native
image, H calibration, recursive child success or membership is supplied.
This is the enumeration stage only: seed admission, root-type pairing,
candidate filter/retention and context-uniform accessibility remain separate. -/
def InternalTermEnumeration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param context gamma types heads typ raw pair size maxLabel seedSize seedLabel out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) seedSize seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.labels n) seedLabel seed param)) →
  Nonempty (Derivation body Delta (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc seedSize))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc seedLabel))) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.enumerated n arity) out seed param)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
