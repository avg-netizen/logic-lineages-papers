module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderInternalAcceptance
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type}
/-- Actual checker mode. No new semantic typing relation. -/
def accepted (H : Program 1) (arguments : Bool) (typ raw gamma : OTerm alpha) : Formula alpha :=
  if arguments then ArgumentsAccepted H typ raw gamma else TermAccepted H typ raw gamma
/-- Guarded helper only: final frozen targets do not assume this guard.
The rejected branch is discharged separately by actual malformed depth zero. -/
def observations (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (xs : Fin 6 → OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
  accepted H arguments (xs 0) raw (xs 1) ⊓
  graph1 (OriginalCodeBoundsRecursion.bounds n) (xs 2) raw ⊓
  graph2 InternalPairing.pairing (xs 2) (xs 3) (xs 4) ⊓
  graph1 (OriginalEnumerationDepth.depth n) (xs 5) raw
/-- Admitted term positivity is a simultaneous induction result, not an endpoint
premise or a false claim about malformed-H accepted terms. -/
def result (arguments : Bool) (size depth : OTerm alpha) : Formula alpha :=
  if arguments then argumentsBound depth size else termBound depth size ⊓ InternalLessThan.strictLess z size
def matrix (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (observations n H arguments (raw.relabel Sum.inl) (fun i => .var (.inr i))).imp
    (result arguments (.var (.inr (3 : Fin 6))) (.var (.inr (5 : Fin 6))))
def AtMode (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n H arguments raw)
def AtRaw (n : Nat) (H : Program 1) (raw : OTerm alpha) : Formula alpha :=
  AtMode n H false raw ⊓ AtMode n H true raw
def predicate (n : Nat) (H : Program 1) : Formula (alpha ⊕ Fin 1) := AtRaw n H (.var (.inr 0))
def BelowRaw (n : Nat) (H : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n H) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Induction
