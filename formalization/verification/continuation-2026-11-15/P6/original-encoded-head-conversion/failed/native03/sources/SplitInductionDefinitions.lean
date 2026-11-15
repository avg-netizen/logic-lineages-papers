module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
def double {alpha : Type} (raw : OTerm alpha) : OTerm alpha := OrdinaryArithmetic.addTerm raw raw
def fields {alpha : Type} (raw out : OTerm alpha) : Formula alpha := graph2 InternalPairing.pairing out raw z
def result {alpha : Type} (raw out : OTerm alpha) : Formula alpha := graph1 split out (double raw)
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (fields (raw.relabel Sum.inl) (.var (.inr 0))).imp (result (raw.relabel Sum.inl) (.var (.inr 0)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitInductionDefinitions
