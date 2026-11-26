module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets

/-- Only an actual observed grammar occurrence, at the exact scope
chosen by the real argument measurement report. -/
def ArgumentOccurrence (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (key depth width : OTerm α) : Prop :=
  ∃ state terms args : OTerm α,
    Nonempty (Derivation body Γ (observed depth (headsTerm s α) (typesTerm s α) width state terms args)) ∧
    Nonempty (Derivation body Γ (memberGraph args key))

structure MeasuredRemaining (P : Programs) (A : Program 1) (s : Settings)
    (body : Positive (Fin 1)) : Prop where
  lambdaBody : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty q : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (lambdaTerm ty q) p vertices ctx result 2 [ty,q] →
    Supplies body Γ goal (fun β j Δ => LambdaFacts P.W s body Δ
      (ctx.relabel j) (result.relabel j) (ty.relabel j) (q.relabel j))
  ordinary : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h a : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (ordinaryKey h a) p vertices ctx result 4 [h,a] →
    ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m d w : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (unary (selectedArgsMeasure A) m (a.relabel j))) →
    Nonempty (Derivation body Δ (codePair m d w)) →
    Supplies body Δ (goal.relabel j) (fun γ g Ξ =>
      ArgumentOccurrence s body Ξ (a.relabel (g ∘ j)) (d.relabel g) (w.relabel g))
  numbered : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h ty k l r : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (numberedTerm h ty k l r) p vertices ctx result 5 [h,ty,k,l,r] →
    ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ml mr dl dr wl wr width : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    NumberedMeasuredArgs A body Δ (k.relabel j) (l.relabel j) (r.relabel j) (p.relabel j)
      ml mr dl dr wl wr width →
    Supplies body Δ (goal.relabel j) (fun γ g Ξ =>
      ArgumentOccurrence s body Ξ (l.relabel (g ∘ j)) (dl.relabel g) (wl.relabel g) ∧
      ArgumentOccurrence s body Ξ (r.relabel (g ∘ j)) (dr.relabel g) (wr.relabel g))

def ExactOpenCoverMeasuredDispatch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p vertices ctx result : OTerm α),
    let P := numberedMeasuredPrograms s V TV M A B T
    MeasuredRemaining P A s body →
    ParentRow P s body Γ raw p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
