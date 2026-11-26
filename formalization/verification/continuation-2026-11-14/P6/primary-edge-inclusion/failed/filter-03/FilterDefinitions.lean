module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Filter
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

def result {alpha : Type} (out candidate : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) out candidate

def fields (E : Program 3) {alpha : Type} (raw reached candidate parameter out : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) raw candidate ⊓
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) reached candidate parameter ⊓
      graph3 (PrimaryExpansion.filterReached E) out raw reached parameter)

def matrix (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields E (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
    (result (.var (.inr 3)) (.var (.inr 1)))
def AtRaw (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix E raw)
def rawPredicate (E : Program 3) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw E (.var (.inr 0))
def BelowRaw (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate E) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Filter
