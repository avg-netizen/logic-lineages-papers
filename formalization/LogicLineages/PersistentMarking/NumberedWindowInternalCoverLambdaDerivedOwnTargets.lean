module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntax)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasure)

abbrev lambdaCover (V T M : Program 1) : Program 3 :=
  selectedCover (lambdaSyntax V T) (lambdaMeasure M)

abbrev lambdaOwnClause {α : Type} (W C : Program 3) (s : Settings)
    (ctx ty q out : OTerm α) : Formula α :=
  (windowAt W ctx ty q).imp
    ((unary (scratchVertices C s) out q).imp (memberGraph out q))

/-- Only the scratch result of this same local typed body is bound.
The induction hypothesis does not quantify over other raw terms. -/
def lambdaLocalIH {α : Type} (W C : Program 3) (s : Settings)
    (ctx ty q : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  allOne (lambdaOwnClause W C s (ctx.relabel j) (ty.relabel j) (q.relabel j) (.var (.inr 0)))

structure Inputs (V T M : Program 1) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p vertices ctx bodyTy ty q : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) (lambdaTerm ty q)))
  measured : Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q)))
  typed : Nonempty (Derivation body Γ (windowAt W ctx bodyTy q))
  localIH : Nonempty (Derivation body Γ (lambdaLocalIH W (lambdaCover V T M) s ctx bodyTy q))
  typeMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))
  held : Nonempty (Derivation body Γ (unary (scratchVertices (lambdaCover V T M) s) vertices (lambdaTerm ty q)))

/-- Genuine lambda parent validity and measure on the two chosen
programs, a typed body/local IH and actual settings member suffice
to prove the same original physical parent own-cover occurrence.
Child validity, coordinates and observations are not hypotheses. -/
def ExactOpenCoverLambdaDerivedOwn : Prop :=
  ∀ (V T M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (p vertices ctx bodyTy ty q : OTerm α),
    Inputs V T M W s body Γ p vertices ctx bodyTy ty q →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
