module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership

def result {alpha : Type} (raw symbols candidate types out value : OTerm alpha) : Formula alpha :=
  ((graph2 contains (numeral 1) out candidate).imp (qualifies raw candidate value)) ⊓
  ((qualifies raw candidate value).imp (graph2 contains (numeral 1) out candidate))
def fields (H : Program 1) {alpha : Type}
    (raw symbols candidate types out value : OTerm alpha) : Formula alpha :=
  graph2 (filterCandidates H) out raw symbols ⊓
  graph2 (OriginalTypedDecoder.packedCheck H) value candidate symbols

def matrix (H : Program 1) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields H (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
    (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))
def AtRaw (H : Program 1) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix H raw)
def rawPredicate (H : Program 1) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw H (.var (.inr 0))
def BelowRaw (H : Program 1) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate H) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Induction
