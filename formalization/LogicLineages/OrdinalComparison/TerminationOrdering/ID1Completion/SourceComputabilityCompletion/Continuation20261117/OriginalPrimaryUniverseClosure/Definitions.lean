module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- The exact original term-universe checker, at the unchanged runtime context. -/
def accepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (typ raw gamma context : OTerm alpha) : Formula alpha :=
  OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    false typ raw gamma context

/-- Internal pointwise invariant. The packed candidate and its observed fields
are independent bound terms; their actual pairing graph connects them. -/
def memberAccepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw gamma context : OTerm alpha) : Formula alpha :=
  (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) reached candidate ⊓
    graph2 InternalPairing.pairing candidate typ raw).imp
      (accepted n arity typ raw gamma context)

/-- All reached members are accepted, quantified INSIDE the original arithmetic
calculus. This is a proof invariant, not a premise of the final target. -/
def allAccepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached gamma context : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock
    (memberAccepted n arity (reached.relabel Sum.inl)
      (.var (.inr (0 : Fin 3))) (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))
      (gamma.relabel Sum.inl) (context.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure
