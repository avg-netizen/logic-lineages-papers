module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261115.OriginalTypeListsMembership.Targets (allMembers)
variable {alpha : Type}
def result (raw allowed : OTerm alpha) : Formula alpha :=
  ((graph2 allTypes (suc z) raw allowed).imp (allMembers raw allowed)) ⊓
  ((allMembers raw allowed).imp (graph2 allTypes (suc z) raw allowed))
def matrix (raw : OTerm alpha) : Formula (alpha ⊕ Fin 1) := result (raw.relabel Sum.inl) (.var (.inr 0))
def AtRaw (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def predicate : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below predicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types
