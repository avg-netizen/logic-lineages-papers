module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Append
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppend (append)
def result {alpha : Type} (raw suffix needle : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) raw needle ⊔ graph2 contains (numeral 1) suffix needle
def fields {alpha : Type} (raw suffix out needle : OTerm alpha) : Formula alpha :=
  graph2 append out raw suffix ⊓ graph2 contains (numeral 1) out needle
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
    (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Append
