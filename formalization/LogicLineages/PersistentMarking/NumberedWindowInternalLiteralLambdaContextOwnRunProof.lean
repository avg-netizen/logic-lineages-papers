module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackUnderlyingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralContextChildOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFallbackDecoderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxDescendingDecoderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaContextOwnRunProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderTransitivity)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunLiftOwnProof (headLess tailLess)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickRename tickFrame moveOrderRight)
open NumberedWindowInternalLiteralDescendingFirstTickProof (FrameDecoder fallbackDecoder)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicFallback)
open NumberedWindowInternalLiteralAtomicFallbackDecoderProof (exact_OpenAtomicFallbackDecoder)
open NumberedWindowInternalLiteralAuxDescendingDecoderProof (exact_OpenAuxiliaryDecoderWith)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback lambdaWitnessTerm)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaFallbackOpenProof
  (exact_OpenLambdaFallbackCall exact_OpenClippedLambdaFallbackCall)
open NumberedWindowInternalLiteralLambdaFallbackForceProof (exact_OpenLambdaFallbackForcesWitness)
open NumberedWindowInternalLiteralLambdaFallbackUnderlyingProof (exact_OpenFullLambdaFallbackUnderlying)
open NumberedWindowInternalLiteralContextChildOwnProof (exact_OpenContextChildOwnRun)

abbrev fullLambdaFallback (other : Program 3) :=
  auxiliaryFallback (atomicFallback (fallback (lambdaFallback other)))

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem lambdaWitnessSmaller (child : OTerm α) :
    D B Γ (ltF child (lambdaWitnessTerm child)) := by
  let inner : OTerm α := rawCons child z
  obtain ⟨a⟩ := headLess (body := B) (Γ := Γ) child z
  obtain ⟨b⟩ : D B Γ (ltF inner (lambdaWitnessTerm child)) := tailLess (numeral 1) inner
  exact closedApply (actualOriginalOrderTransitivity B α child inner (lambdaWitnessTerm child))
    ⟨Derivation.conjunctionIntroduction a b⟩

/-- A successful parent with a genuine lambda-context callback reaches
the exact raw body transition at its own original certificate fuel. -/
theorem exact_OpenLambdaContextOwnRun (P other : Program 3) (q w r n : OTerm α) (goal : Formula α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (first : D B Γ (TickAt P (fullLambdaFallback other) z (suc n) q w r))
    (callback : D B Γ (programGraph (fullLambdaFallback other) (suc n) ![q,w,r]))
    (accepted : D B Γ (bit (ownRun P (fullLambdaFallback other)) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a child e b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaParts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d a child e b →
      D B Δ (bit (ownRun P (fullLambdaFallback other)) ![a,child,b]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let F := fullLambdaFallback other
  let P₀ := fallback (lambdaFallback other)
  have decode : FrameDecoder F := exact_OpenAuxiliaryDecoderWith (atomicFallback P₀)
    (exact_OpenAtomicFallbackDecoder P₀ (fallbackDecoder (lambdaFallback other)))
  have checked := exact_OpenFullLambdaFallbackUnderlying other q w r n head callback
  have tag := exact_OpenLambdaFallbackForcesWitness other q w r n head checked
  have real := exact_OpenClippedLambdaFallbackCall other q w r n checked
  apply exact_OpenLambdaFallbackCall other q w r n goal tag real
  intro β j Δ d a child e b keep parts frame
  have tick := renameInto first j Δ keep
  rw [tickRename,zRelabel,sucRelabel] at tick
  have atChild := tickFrame P F z (suc (n.relabel j)) (frameValueTerm a child b)
    (q.relabel j) (w.relabel j) (r.relabel j) tick frame
  obtain ⟨wEq⟩ := parts.witness
  have smaller := moveOrderRight child (lambdaWitnessTerm child) (w.relabel j) (lambdaWitnessSmaller child) ⟨symm wEq⟩
  have holds := moveBit (ownRun P F) q w r j Δ keep accepted
  exact use β j Δ d a child e b keep parts
    (exact_OpenContextChildOwnRun P F decode (q.relabel j) (w.relabel j) (r.relabel j) a child b atChild smaller holds)

#print axioms lambdaWitnessSmaller
#print axioms exact_OpenLambdaContextOwnRun
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaContextOwnRunProof
