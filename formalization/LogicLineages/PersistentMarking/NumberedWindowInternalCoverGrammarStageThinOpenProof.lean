module
/- Thin arbitrary-open derivation recut of NumberedWindowInternalCoverGrammarStageChecks; original statement and physical programs unchanged. -/

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageThinStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageThinOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRawListRecursionSupportProof (recursionRecover)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverGrammarStageTargets
open NumberedWindowInternalCoverGrammarStageThinStepProof (completedTerms stepMember)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem termsRename {β : Type} (P : Program 5) (A : Program 2)
    (out d H K maxNumeral : OTerm α) (j : α → β) :
    (termsGraph P A out d H K maxNumeral).relabel j =
    termsGraph P A (out.relabel j) (d.relabel j) (H.relabel j) (K.relabel j) (maxNumeral.relabel j) := by
  simp only [termsGraph,programRename,quadInputsRename]

private theorem atSuccessor (P : Program 5) (A : Program 2)
    (old prev out d H K maxNumeral dom cod fn arg : OTerm α)
    (previous : Nonempty (Derivation body Γ (programGraph (grammarStage P A) old ![d,H,K,maxNumeral])))
    (priorTerms : Nonempty (Derivation body Γ (unary ID1Completion.InternalUnpair.left prev old)))
    (next : Nonempty (Derivation body Γ (termsGraph P A out (suc d) H K maxNumeral)))
    (domIn : Nonempty (Derivation body Γ (memberGraph K dom)))
    (codIn : Nonempty (Derivation body Γ (memberGraph K cod)))
    (fnIn : Nonempty (Derivation body Γ (memberGraph prev fn)))
    (argIn : Nonempty (Derivation body Γ (memberGraph prev arg))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg))) := by
  let stage := grammarStage P A
  apply programCases stage ![suc d,H,K,maxNumeral] _
  intro β j Δ state keep final
  rw [graphRename,auxiliaryRename]
  simp only [quadInputsRename,sucRelabel] at final
  have prior := renameInto previous j Δ keep
  simp only [programRename,quadInputsRename] at prior
  have report := renameInto priorTerms j Δ keep
  rw [unaryRename] at report
  have specified := renameInto next j Δ keep
  rw [termsRename,sucRelabel] at specified
  let d' := d.relabel j
  let old' := old.relabel j
  let out' := out.relabel j
  let H' := H.relabel j
  let K' := K.relabel j
  let m' := maxNumeral.relabel j
  let params : Fin 3 → OTerm β := ![H',K',m']
  have read : Nonempty (Derivation body Δ (unary ID1Completion.InternalUnpair.left out' state)) :=
    unaryRecover ID1Completion.InternalUnpair.left stage out' state ![suc d',H',K',m'] specified final
  have align (n : OTerm β) : (![n,H',K',m'] : Fin 4 → OTerm β) = Fin.cons n params := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  have measuredPrior : Nonempty (Derivation body Δ (programGraph stage old' (Fin.cons d' params))) := by
    rw [← align]
    exact prior
  have measuredFinal : Nonempty (Derivation body Δ (programGraph stage state (Fin.cons (suc d') params))) := by
    rw [← align]
    exact final
  have nativeStep := recursionRecover initialLayer (grammarStep P A) state old' d' params measuredPrior measuredFinal
  have stepTape : (Fin.cons d' (Fin.cons old' params) : Fin 5 → OTerm β) = ![d',old',H',K',m'] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  rw [stepTape] at nativeStep
  have terms := completedTerms P A state out' ![d',old',H',K',m'] nativeStep read
  have hDom := renameInto domIn j Δ keep
  have hCod := renameInto codIn j Δ keep
  have hFn := renameInto fnIn j Δ keep
  have hArg := renameInto argIn j Δ keep
  simp only [graphRename] at hDom hCod hFn hArg
  exact stepMember P out' d' old' H' K' m' (prev.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    report terms hDom hCod hFn hArg

theorem exact_OpenGrammarStageAuxMember : ExactOpenGrammarStageAuxMember := by
  intro P A body α Γ prev out d H K maxNumeral dom cod fn arg previous next domIn codIn fnIn argIn
  let stage := grammarStage P A
  apply programCases stage ![d,H,K,maxNumeral] _
  intro β j Δ old keep actual
  rw [graphRename,auxiliaryRename]
  simp only [quadInputsRename] at actual
  have pre := renameInto previous j Δ keep
  have post := renameInto next j Δ keep
  rw [termsRename] at pre
  rw [termsRename,sucRelabel] at post
  have p : Nonempty (Derivation body Δ (unary ID1Completion.InternalUnpair.left (prev.relabel j) old)) :=
    unaryRecover ID1Completion.InternalUnpair.left stage (prev.relabel j) old
      ![d.relabel j,H.relabel j,K.relabel j,maxNumeral.relabel j] pre actual
  have hDom := renameInto domIn j Δ keep
  have hCod := renameInto codIn j Δ keep
  have hFn := renameInto fnIn j Δ keep
  have hArg := renameInto argIn j Δ keep
  simp only [graphRename] at hDom hCod hFn hArg
  exact atSuccessor P A old (prev.relabel j) (out.relabel j) (d.relabel j) (H.relabel j) (K.relabel j)
    (maxNumeral.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    actual p post hDom hCod hFn hArg

#print axioms exact_OpenGrammarStageAuxMember

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageThinOpenProof
