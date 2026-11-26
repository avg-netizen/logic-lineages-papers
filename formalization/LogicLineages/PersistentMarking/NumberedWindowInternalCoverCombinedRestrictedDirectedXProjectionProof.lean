module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProjectionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consDestruction)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable scratchBase scratchStep)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
  (binaryInputsRename tripleInputsRename quadInputsRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selectedReports (a b : OTerm α) :
    ∀ i : Fin 3, Nonempty (Derivation body Γ (programGraph
      ((![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2] : Fin 3 → Program 2) i)
      ((![pairTerm a b,z,z] : Fin 3 → OTerm α) i) ![a,b])) := by
  intro i
  exact Fin.cases (pairGraph a b)
    (Fin.cases (zeroConstantValue ![a,b]) (Fin.cases (zeroConstantValue ![a,b]) (fun k => Fin.elim0 k))) i

theorem exact_OpenSelectedMemoProjection : ExactOpenSelectedMemoProjection := by
  intro R body α Γ out a b
  let parts : Fin 3 → Program 2 := ![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2]
  let values : Fin 3 → OTerm α := ![pairTerm a b,z,z]
  constructor
  · intro h
    exact compositionRecover (scratchRow (constantZero 2) R) parts out ![a,b] values h (selectedReports a b)
  · intro h
    exact compositionValue (scratchRow (constantZero 2) R) parts out ![a,b] values h (selectedReports a b)

#print axioms exact_OpenSelectedMemoProjection
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProjectionProof
