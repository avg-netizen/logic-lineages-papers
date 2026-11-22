module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)

/-- A genuine selected lexical-window report on a literal lambda exposes
the actual positive deepest control on that same parent tape, with its
possibly different output kept in the genuine object proof scope. -/
def ExactOpenCoverLambdaPositiveControl : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom q result : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (windowGraph (lambdaLexicalWindow s B T) ctx result (lambdaTerm dom q))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (control : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph B (suc control)
        ![ctx.relabel j,lambdaTerm (dom.relabel j) (q.relabel j)])) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlTargets
