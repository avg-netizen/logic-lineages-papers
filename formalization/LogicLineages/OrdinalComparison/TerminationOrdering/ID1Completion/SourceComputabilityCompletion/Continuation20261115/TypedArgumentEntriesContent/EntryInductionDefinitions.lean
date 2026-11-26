module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114

def fields {alpha : Type} (H : Program 1) (raw types gamma param entries entry tau child : OTerm alpha) : Formula alpha :=
  OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma ⊓
  graph2 ArgumentEntriesRecursor.extract (suc entries) raw param ⊓
  graph2 contains (numeral 1) entries entry ⊓
  graph2 InternalPairing.pairing entry tau child
def result {alpha : Type} (H : Program 1) (raw types gamma param entries entry tau child : OTerm alpha) : Formula alpha :=
  OriginalTypedDecoderInternalAcceptance.TermAccepted H tau child gamma
def matrix {alpha : Type} (H : Program 1) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (fields H (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
  (result H (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)))
def AtRaw {alpha : Type} (H : Program 1) (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix H raw)
def rawPredicate {alpha : Type} (H : Program 1) : Formula (alpha ⊕ Fin 1) := AtRaw H (.var (.inr 0))
def BelowRaw {alpha : Type} (H : Program 1) (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate H) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionDefinitions
