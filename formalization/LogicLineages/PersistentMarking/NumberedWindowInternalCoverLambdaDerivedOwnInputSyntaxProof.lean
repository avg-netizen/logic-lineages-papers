module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel zRelabel)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename windowSubst memberSubst)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem ihSubst (W C : Program 3) (s : Settings) (ctx ty q : OTerm α)
    (ts : α → OTerm β) :
    (lambdaLocalIH W C s ctx ty q).subst (fun a => emb (ts a)) =
      lambdaLocalIH W C s (ctx.subst ts) (ty.subst ts) (q.subst ts) := by
  simp only [lambdaLocalIH,lambdaOwnClause,allEmbeddedSubst,impSubst,windowSubst,
    unarySubst,memberSubst,liftTermSubst] <;> rfl

theorem ihRename (W C : Program 3) (s : Settings) (ctx ty q : OTerm α) (j : α → β) :
    (lambdaLocalIH W C s ctx ty q).relabel j =
      lambdaLocalIH W C s (ctx.relabel j) (ty.relabel j) (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (lambdaLocalIH W C s ctx ty q).subst (fun a => emb (.var (j a))) = _
  rw [ihSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem specializeIH (W C : Program 3) (s : Settings) (ctx ty q out : OTerm α)
    (h : Nonempty (Derivation body Γ (lambdaLocalIH W C s ctx ty q))) :
    Nonempty (Derivation body Γ (lambdaOwnClause W C s ctx ty q out)) := by
  obtain ⟨h⟩ := h
  have atOut := Derivation.universalElimination (emb out) h
  simpa only [lambdaLocalIH,lambdaOwnClause,instantiate,bindEmbedding,impSubst,
    windowSubst,unarySubst,memberSubst,liftBind,varBind] using (Nonempty.intro atOut)

theorem inputsRename (V T M : Program 1) (W : Program 3) (s : Settings)
    (p vertices ctx bodyTy ty q : OTerm α) (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (paid : Inputs V T M W s body Γ p vertices ctx bodyTy ty q) :
    Inputs V T M W s body Δ (p.relabel j) (vertices.relabel j) (ctx.relabel j)
      (bodyTy.relabel j) (ty.relabel j) (q.relabel j) := by
  constructor
  · have actual := renameInto paid.valid j Δ keep
    simpa only [unaryRename,lambdaRename,sucRelabel,zRelabel] using actual
  · have actual := renameInto paid.measured j Δ keep
    simpa only [unaryRename,lambdaRename] using actual
  · have actual := renameInto paid.typed j Δ keep
    simpa only [windowRename] using actual
  · have actual := renameInto paid.localIH j Δ keep
    simpa only [ihRename] using actual
  · have actual := renameInto paid.typeMember j Δ keep
    simpa only [graphRename,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.held j Δ keep
    simpa only [unaryRename,lambdaRename] using actual

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
