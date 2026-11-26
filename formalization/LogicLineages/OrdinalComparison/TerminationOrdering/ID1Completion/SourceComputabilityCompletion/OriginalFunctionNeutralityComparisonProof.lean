module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityComparisonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalFunctionNeutrality OriginalFunctionNeutralityFullFoldProof
open OriginalConstructorShapeApplicationProof (iffCompose iffFlip)
open InternalParameterizedCanonicalResultFold (sourcePremises foldGraph)
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof

/-- Reflect the same neutral observer from a common actual canonical output
to both raw sources. Both original source premises and fold graphs remain. -/
theorem actualOriginalFunctionNeutralityCanonicalComparison :
    OriginalFunctionNeutralityTargets.ActualOriginalFunctionNeutralityCanonicalComparison := by
  intro data window body alpha Delta out left right leftType rightType parameter value
  let selected := selectedData data window
  let P := windowGraph window left parameter ⊓
    (windowGraph window right parameter ⊓
      (sourcePremises selected left leftType parameter ⊓
        (sourcePremises selected right rightType parameter ⊓
          (foldGraph selected out left parameter ⊓ foldGraph selected out right parameter))))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := andRight hp
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  obtain ⟨hlaw⟩ := fullFoldMarkPreservation data window body alpha (P :: Delta)
    out left leftType parameter value
  obtain ⟨hrlaw⟩ := fullFoldMarkPreservation data window body alpha (P :: Delta)
    out right rightType parameter value
  obtain ⟨hleftPre⟩ := andIntro (andLeft hp) (andIntro (andLeft h2) (andLeft h4))
  obtain ⟨hrightPre⟩ := andIntro (andLeft h1) (andIntro (andLeft h3) (andRight h4))
  have hleft := Derivation.implicationElimination hlaw hleftPre
  have hright := Derivation.implicationElimination hrlaw hrightPre
  obtain ⟨h⟩ := iffCompose (markGraph value left) (markGraph value out) (markGraph value right)
    (iffFlip (markGraph value out) (markGraph value left) ⟨hleft⟩) ⟨hright⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityComparisonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityComparisonProof
