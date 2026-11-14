module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Any
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def result (E : Program 3) {alpha : Type} (raw candidate parameter : OTerm alpha) : Formula alpha := sourceWitness E raw candidate parameter

def fields (E : Program 3) {alpha : Type} (raw candidate parameter : OTerm alpha) : Formula alpha :=
  graph3 (PrimaryExpansion.anyEdge E) (numeral 1) raw candidate parameter

def matrix (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (fields E (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (result E (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)))
def AtRaw (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix E raw)
def rawPredicate (E : Program 3) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw E (.var (.inr 0))
def BelowRaw (E : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate E) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Any
