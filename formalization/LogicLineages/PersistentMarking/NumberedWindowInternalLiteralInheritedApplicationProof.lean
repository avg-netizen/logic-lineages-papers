module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoFirstChildProof
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm graph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalNeutralFactsTargets (direct inherited)

variable {α : Type} {Γ : List (Formula α)}

private theorem directRename {β : Type} (S : Data) (h : Program 3) (c : Nat) (x y : OTerm α) (j : α → β) :
    (direct S h c x y).relabel j = direct S h c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (direct S h c x y).subst (fun a => emb (.var (j a))) = _
  simp only [direct,edgeSubst,← termRelabelAsSubst]

theorem exact_InheritedApplicationRename {β : Type} (S : Data) (p h : Program 3) (c : Nat)
    (x u y : OTerm α) (j : α → β) :
    (inherited S p h c x u y).relabel j = inherited S p h c (x.relabel j) (u.relabel j) (y.relabel j) := by
  unfold inherited
  rw [existsRename]
  simp only [conjunctionRename,directRename,acceptsRename,Term.relabel_relabel]
  rfl

theorem exact_OpenInheritedApplicationIntro (S : Data) (p h : Program 3) (c : Nat)
    (x u y w : OTerm α)
    (step : D (sourceBody S c) Γ (direct S h c x w))
    (application : D (sourceBody S c) Γ (accepts p w u y)) :
    D (sourceBody S c) Γ (inherited S p h c x u y) := by
  unfold inherited
  obtain ⟨step⟩ := step
  obtain ⟨applyAt⟩ := application
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb w)
  simpa only [instantiate,bindEmbedding,conjunctionSubst,direct,edgeSubst,acceptsSubst,liftBind,varBind]
    using Derivation.conjunctionIntroduction step applyAt

theorem exact_OriginalApplicationAcceptedGraph (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f,u,y] := rfl

#print axioms exact_OriginalApplicationAcceptedGraph
#print axioms exact_InheritedApplicationRename
#print axioms exact_OpenInheritedApplicationIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof
