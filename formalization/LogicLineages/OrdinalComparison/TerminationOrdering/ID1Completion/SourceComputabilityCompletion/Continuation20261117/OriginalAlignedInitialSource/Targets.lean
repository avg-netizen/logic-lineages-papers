module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion TwoSol20261113.CalibratedPrimary
open Continuation20261114 Continuation20261115 Continuation20261116
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Companion at explicit NEW aligned input tuple. No calibration or source/window activation premise. -/
def InternalAlignedSource : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input parameter typ raw context gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
  Nonempty (Derivation body Delta
    ((graph2 (installedInputs n arity p).base.oldSource (numeral 1) input parameter).iff
      (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context ⊓
        OriginalUniverseDecoderInternalAcceptance.TermAccepted
          (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
          (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Targets
