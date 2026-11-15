module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
def AtRaw {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha :=
  ((graph1 (symbols n) (numeral 1) raw).imp (Targets.boundedMembers n raw)) ⊓
    ((Targets.boundedMembers n raw).imp (graph1 (symbols n) (numeral 1) raw))
def rawPredicate {alpha : Type} (n : Nat) : Formula (alpha ⊕ Fin 1) := AtRaw n (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate n) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionDefinitions
