module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
/-- Literal arrow subtype closure, asserted inside the object language. No
source-head or window acceptance premise is built into this condition. -/
def closureMatrix {alpha : Type} (types : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (graph2 InternalPairing.pairing (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    member (types.relabel Sum.inl) (suc (.var (.inr 0)))).imp
      (member (types.relabel Sum.inl) (.var (.inr 1)) ⊓
       member (types.relabel Sum.inl) (.var (.inr 2)))
def ArrowClosed {alpha : Type} (types : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (closureMatrix types)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion
