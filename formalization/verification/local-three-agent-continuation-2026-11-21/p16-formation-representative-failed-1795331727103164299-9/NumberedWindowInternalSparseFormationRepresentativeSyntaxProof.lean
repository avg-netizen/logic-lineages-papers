module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (auxiliarySubst)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

theorem formationSubst {α β : Type} (W : Program 3) (ctx dom cod arg : OTerm α) (ts : α → OTerm β) :
    (formation W ctx dom cod arg).subst (fun a => emb (ts a)) =
    formation W (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) := by
  simp only [formation,allEmbeddedSubst,impSubst,windowSubst,auxiliarySubst,liftTermSubst,rawConsSubst]
  rfl

theorem formationRename {α β : Type} (W : Program 3) (ctx dom cod arg : OTerm α) (j : α → β) :
    (formation W ctx dom cod arg).relabel j = formation W (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (arg.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formation W ctx dom cod arg).subst (fun a => emb (.var (j a))) = _
  rw [formationSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem atFunction {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (W : Program 3)
    (ctx dom cod arg f : OTerm α) (d : Derivation body Γ (formation W ctx dom cod arg)) :
    Nonempty (Derivation body Γ ((windowAt W ctx (rawCons dom cod) f).imp
      (windowAt W ctx cod (auxiliaryTerm dom cod f arg)))) := by
  have applied := Derivation.universalElimination (emb f) d
  simpa only [instantiate,bindEmbedding,impSubst,windowSubst,auxiliarySubst,liftBind,varBind] using
    Nonempty.intro applied

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeSyntaxProof
