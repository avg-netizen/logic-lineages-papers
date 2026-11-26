module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedGrammarHeadProviderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadProviderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadProviderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject normalizeRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase namedSharedMeasure)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverTypeOnlyHeadProviderProof (exact_OpenCoverTypeOnlyHeadProvider)
open NumberedWindowInternalCoverNamedGrammarHeadProviderProof (exact_OpenCoverNamedGrammarHead)
open NumberedWindowInternalCoverMixedLeafArgumentTargets

theorem chosenHeadUnion (F X Y : Program 1) (s : Settings) (body : Positive (Fin 1))
    (left : HeadProvider F X s body) (right : HeadProvider F Y s body) :
    HeadProvider F (unionHeadGuard X Y) s body := by
  intro α Γ h p Q chosen measured next
  let L := unary X (suc z) h
  apply formulaCases L Q
  · apply left α (L :: Γ) h p Q ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp measured L)
    intro β j Δ d w state terms args keep pair actual
    exact next β j Δ d w state terms args (fun f hf => keep f (List.mem_cons_of_mem _ hf)) pair actual
  · have reject := normalizeReject X ![h] (body := body) (Gamma := L.not :: Γ)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have branch := zeroBranchElim (normalize X) (normalize Y) (literal 1 1) (suc z) ![h]
      reject (withHyp chosen L.not)
    have accepted := normalizeRecover Y ![h] branch
    apply right α (L.not :: Γ) h p Q accepted (withHyp measured L.not)
    intro β j Δ d w state terms args keep pair actual
    exact next β j Δ d w state terms args (fun f hf => keep f (List.mem_cons_of_mem _ hf)) pair actual

theorem exact_OpenCoverMixedLeafHeadProvider : ExactOpenCoverMixedLeafHeadProvider := by
  intro s M body
  let F := namedSharedMeasure M
  have named := chosenHeadUnion F (namedGrammarHead s false) (namedGrammarHead s true) s body
    (exact_OpenCoverNamedGrammarHead s false M body) (exact_OpenCoverNamedGrammarHead s true M body)
  exact chosenHeadUnion F _ _ s body (exact_OpenCoverTypeOnlyHeadProvider s (namedMeasureBase M) body) named

#print axioms chosenHeadUnion
#print axioms exact_OpenCoverMixedLeafHeadProvider

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadProviderProof
