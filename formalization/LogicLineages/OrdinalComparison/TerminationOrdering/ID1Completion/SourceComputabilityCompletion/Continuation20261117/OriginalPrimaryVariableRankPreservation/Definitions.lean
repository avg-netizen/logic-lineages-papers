module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
def accepted {alpha : Type} (R : Program 1) (ref x : OTerm alpha) : Formula alpha := graph1 R ref x
 def memberAccepted {alpha : Type} (R : Program 1) (ref reached : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0))).imp
    (accepted R (ref.relabel Sum.inl) (.var (.inr 0)))
def allAccepted {alpha : Type} (R : Program 1) (ref reached : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (memberAccepted R ref reached)
def forwardMatrix {alpha : Type} (R : Program 1) (E : Program 3) (ref parameter : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  let x : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let y : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  (accepted R (ref.relabel Sum.inl) x ⊓ graph3 E (numeral 1) x y (parameter.relabel Sum.inl)).imp
    (accepted R (ref.relabel Sum.inl) y)
def forwardClosed {alpha : Type} (R : Program 1) (E : Program 3) (ref parameter : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (forwardMatrix R E ref parameter)
/-- Bookkeeping wrappers ignore pool/seed: exact scalar invariant only. -/
def acceptedAt {alpha : Type} (R : Program 1) (_pool ref _seed x : OTerm alpha) : Formula alpha := accepted R ref x
def memberAcceptedAt {alpha : Type} (R : Program 1) (pool ref seed reached : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0))).imp
    (acceptedAt R (pool.relabel Sum.inl) (ref.relabel Sum.inl) (seed.relabel Sum.inl) (.var (.inr 0)))
def allAcceptedAt {alpha : Type} (R : Program 1) (pool ref seed reached : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (memberAcceptedAt R pool ref seed reached)
def forwardMatrixAt {alpha : Type} (R : Program 1) (E : Program 3) (_pool ref parameter : OTerm alpha) : Formula (alpha ⊕ Fin 2) := forwardMatrix R E ref parameter
def forwardClosedAt {alpha : Type} (R : Program 1) (E : Program 3) (pool ref parameter : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (forwardMatrixAt R E pool ref parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation
