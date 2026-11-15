module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Original supplier inputs [encoded node, parameter]; parameter is unused. -/
def source : Program 2 := leftOf (.projection 0)
def target : Program 2 := rightOf (.projection 0)
def sourceAccepted (n : Nat) : Program 2 := .composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => source)
def targetAccepted (n : Nat) : Program 2 := .composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => target)
def accepted (n : Nat) : Program 2 := InternalAcceptance.conjunction (sourceAccepted n) (targetAccepted n)
def decodedCross : Program 2 := .composition NumericDependencyCross.rawDependencies ![source,target]
/-- Literal pair decoder guard. Rejection returns numbersNumber [] = 0; acceptance
retains the original ordered cross, including duplicates. Not an installation. -/
def dependencies (n : Nat) : Program 2 := InternalAcceptance.branch (accepted n) (constant 2 0) decodedCross
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies
