module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (headTransport programRename valueUnique)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename quadInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverGrammarStageTargets (grammarTerms termsGraph)
open NumberedWindowInternalCoverGrammarStageChecks (exact_OpenGrammarStageAuxMember)
open NumberedWindowInternalFactoredAuxOwnCoverTargets
open NumberedWindowInternalFactoredAuxOwnCoverProgramProof (actualScratch)

attribute [local irreducible] programGraph

theorem exact_OpenFactoredAuxCoverAtTerms : ExactOpenFactoredAuxCoverAtTerms := by
  intro V M P A s body α Γ m depth maxNumeral prev vertices dom cod fn arg parent C
    valid measure pair prior current domIn codIn fnIn argIn
  obtain ⟨⟨option⟩,⟨verticesRun⟩⟩ :=
    actualScratch V M P A s m depth maxNumeral vertices parent valid measure pair current
  obtain ⟨occurs⟩ := exact_OpenGrammarStageAuxMember P A body α Γ prev vertices depth
    (headsTerm s α) (typesTerm s α) maxNumeral dom cod fn arg prior current domIn codIn fnIn argIn
  exact ⟨Derivation.conjunctionIntroduction option (Derivation.conjunctionIntroduction verticesRun occurs)⟩

theorem exact_OpenFactoredAuxCoverMembership : ExactOpenFactoredAuxCoverMembership := by
  intro V M P A s body α Γ m depth maxNumeral prev vertices dom cod fn arg parent C
    valid measure pair prior domIn codIn fnIn argIn existing
  apply programCases (grammarTerms P A) ![suc depth,headsTerm s α,typesTerm s α,maxNumeral] _
  intro β j Δ actual keep stage
  rw [graphRename,auxiliaryRename]
  have current : Nonempty (Derivation body Δ
      (termsGraph P A actual (suc (depth.relabel j)) (headsTerm s β) (typesTerm s β)
        (maxNumeral.relabel j))) := by
    simpa only [quadInputsRename,sucRelabel,headsTerm,typesTerm,numeralRename] using stage
  have hv := renameInto valid j Δ keep
  have hm := renameInto measure j Δ keep
  have hp := renameInto pair j Δ keep
  have hn := renameInto prior j Δ keep
  have hd := renameInto domIn j Δ keep
  have hc := renameInto codIn j Δ keep
  have hf := renameInto fnIn j Δ keep
  have ha := renameInto argIn j Δ keep
  have he := renameInto existing j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,parent,auxiliaryRename] at hv hm he
  simp only [measurePair,programRename,binaryInputsRename,sucRelabel] at hp
  simp only [termsGraph,programRename,quadInputsRename,headsTerm,typesTerm,numeralRename] at hn
  simp only [graphRename,typesTerm,numeralRename] at hd hc
  simp only [graphRename] at hf ha
  obtain ⟨checked⟩ := exact_OpenFactoredAuxCoverAtTerms V M P A s body β Δ (m.relabel j)
    (depth.relabel j) (maxNumeral.relabel j) (prev.relabel j) actual
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) hv hm hp hn current hd hc hf ha
  have forward := Derivation.conjunctionRight checked
  have eq := valueUnique (scratchVertices C s) actual (vertices.relabel j)
    ![auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)]
    ⟨Derivation.conjunctionLeft forward⟩ he
  exact headTransport scratchMember (suc z) actual (vertices.relabel j)
    ![auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)]
    eq ⟨Derivation.conjunctionRight forward⟩

#print axioms exact_OpenFactoredAuxCoverAtTerms
#print axioms exact_OpenFactoredAuxCoverMembership

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverChecks
