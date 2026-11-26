module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareDefinitions
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus (Formula)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalThinUncoveredCount (count bounded)
open NumberedWindowInternalScratchInclusionThinProof (included)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

namespace Compare
def newness {alpha : Type} (raw left right candidate : OTerm alpha) : Formula alpha :=
  graph2 scratchMember (suc z) raw candidate ⊓
    ((graph2 scratchMember (suc z) left candidate).not ⊓ graph2 scratchMember (suc z) right candidate)
def result {alpha : Type} (raw left right leftCount rightCount candidate : OTerm alpha) : Formula alpha :=
  bounded rightCount leftCount ⊓ ((newness raw left right candidate).imp
    (ltF rightCount leftCount))
def fields {alpha : Type} (raw left right leftCount rightCount _candidate : OTerm alpha) : Formula alpha :=
  included left right ⊓
    (graph2 count leftCount raw left ⊓ graph2 count rightCount raw right)
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4))).imp
  (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := below rawPredicate raw
end Compare

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareDefinitions
