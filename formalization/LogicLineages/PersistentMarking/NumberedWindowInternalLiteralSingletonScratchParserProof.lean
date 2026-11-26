module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchParserProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalOriginalRawConsUnionReportThinProof (actualRawConsParser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalLiteralSingletonScratchTargets

theorem exact_ParsedSingletonScratch : ExactParsedSingletonScratch := by
  intro B α Γ head decoded actual
  apply programCases consCode ![head,z] (consGraph decoded head z)
  intro β ρ Δ selected keep chosen
  rw [consGraphRename,zRelabel]
  have picked : Nonempty (Derivation B Δ (programGraph consCode selected ![head.relabel ρ,z])) := by
    simpa only [binaryInputsRename,zRelabel] using chosen
  have built := actualRawConsParser (head.relabel ρ) z z selected exact_OriginalSparseParserNil picked
  have held : Nonempty (Derivation B Δ (unary parser (suc (decoded.relabel ρ))
      (rawCons (head.relabel ρ) z))) := by
    simpa only [singletonCode,rawConsRename,zRelabel] using renameParser (singletonCode head) decoded actual ρ Δ keep
  obtain ⟨same⟩ := valueUnique parser (suc selected) (suc (decoded.relabel ρ))
    ![rawCons (head.relabel ρ) z] built held
  exact outputTransport consCode selected (decoded.relabel ρ) ![head.relabel ρ,z] ⟨cancelSuc same⟩ picked

#print axioms exact_ParsedSingletonScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchParserProof
