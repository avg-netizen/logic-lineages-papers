module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
def accepted {alpha : Type} (pool carrier seed x : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) pool x ⊓
    ((graph2 contains (numeral 1) carrier x).imp (graph2 contains (numeral 1) carrier seed))
def memberAccepted {alpha : Type} (pool carrier seed reached : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0))).imp
    (accepted (pool.relabel Sum.inl) (carrier.relabel Sum.inl) (seed.relabel Sum.inl) (.var (.inr 0)))
def allAccepted {alpha : Type} (pool carrier seed reached : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (memberAccepted pool carrier seed reached)
def backwardMatrix {alpha : Type} (E : Program 3) (pool carrier parameter : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  let x : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let y : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  (graph2 contains (numeral 1) (pool.relabel Sum.inl) x ⊓
    (graph2 contains (numeral 1) (carrier.relabel Sum.inl) y ⊓
      graph3 E (numeral 1) x y (parameter.relabel Sum.inl))).imp
    (graph2 contains (numeral 1) (carrier.relabel Sum.inl) x)
def backClosed {alpha : Type} (E : Program 3) (pool carrier parameter : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (backwardMatrix E pool carrier parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership
