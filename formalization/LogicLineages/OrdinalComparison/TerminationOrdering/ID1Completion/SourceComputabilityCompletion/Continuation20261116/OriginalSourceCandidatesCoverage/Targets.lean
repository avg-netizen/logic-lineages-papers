module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
/-- Same-seed source coverage of the ORIGINAL candidate program. Explicit
source conditions include the original Context decoder and source acceptance
of both the seed and candidate at the same root type and Gamma. They are not
an assumed typed-seed admission, packed-check success, image, Fields or depth
oracle. The actual seed and candidate pairing observations fix root-type
identity. All old metadata/capacity observations retain their original roles.
No WindowPrimary preservation, prior existential-Q identity or concrete H
calibration is claimed; this is membership in the fixed literal Q only. -/
def InternalTermCandidates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param context gamma types heads typ seedRaw raw candidate pair size maxLabel seedSize seedLabel out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) seedSize seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.labels n) seedLabel seed param)) →
  Nonempty (Derivation body Delta (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ seedRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ raw)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ seedRaw gamma context)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc seedSize))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc seedLabel))) →
  Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity H) out seed param)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Targets
