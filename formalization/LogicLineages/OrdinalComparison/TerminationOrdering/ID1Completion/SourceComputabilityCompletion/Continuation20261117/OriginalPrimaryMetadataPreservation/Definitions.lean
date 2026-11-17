module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- Fixed original metadata: same root type and the SAME complete bounds output.
The actual endpoint's independently observed bounds are compared by functionality. -/
def accepted {alpha : Type} (n : Nat) (_arity : Fin n → Nat)
    (typ raw rootTypeRef boundsRef : OTerm alpha) : Formula alpha :=
  InternalTagArithmeticSyntaxProof.eqn rootTypeRef typ ⊓
    graph1 (OriginalCodeBoundsRecursion.bounds n) boundsRef raw

/-- Internal pointwise invariant. The packed candidate and its observed fields
are independent bound terms; their actual pairing graph connects them. -/
def memberAccepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw rootTypeRef boundsRef : OTerm alpha) : Formula alpha :=
  (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) reached candidate ⊓
    graph2 InternalPairing.pairing candidate typ raw).imp
      (accepted n arity typ raw rootTypeRef boundsRef)

/-- All reached members are accepted, quantified INSIDE the original arithmetic
calculus. This is a proof invariant, not a premise of the final target. -/
def allAccepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached rootTypeRef boundsRef : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock
    (memberAccepted n arity (reached.relabel Sum.inl)
      (.var (.inr (0 : Fin 3))) (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))
      (rootTypeRef.relabel Sum.inl) (boundsRef.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation
