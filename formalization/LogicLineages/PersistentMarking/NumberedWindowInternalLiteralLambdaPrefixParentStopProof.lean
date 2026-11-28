module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixBypassProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixParentStopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalControlGraphSupportProof (headTransport programRename zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalNumericIterationSupportProof (repeatZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
  (exact_OpenPrefixTickAtFrame exact_OpenPrefixTickTerminal)
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
  (exact_OpenPrefixOwnIntroduce prefixStartTermRename)
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (fiveInputsRename)
open NumberedWindowInternalLiteralTickIterationProof (shiftLate)
open NumberedWindowInternalLiteralTickIterationFixedProof (exact_OpenTickIterationFixed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem stopTick (W : Program 3) (c t q w r : OTerm α)
    (stopped : D B Γ (programGraph isLambdaPrefix z ![c,t,q,w,r])) :
    D B Γ (programGraph (prefixTick W) (stateTerm (suc z) z) ![prefixStartTerm c t q w r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  let terminal : OTerm α := stateTerm (suc z) z
  have accept : D B Γ (programGraph prefixAccept terminal xs) :=
    emitGraph _ _ (suc z) z xs (oneConstantValue xs) (constantZeroValue xs)
  have live : D B Γ (programGraph (prefixLive W) terminal xs) :=
    zeroBranchIntro isLambdaPrefix prefixAccept _ terminal xs stopped accept
  exact exact_OpenPrefixTickAtFrame W (suc z) c t q w r terminal live

private theorem finishParent (W : Program 3) (c t q w r fuel next out : OTerm α)
    (budget : D B Γ (eqn w (suc fuel)))
    (first : D B Γ (programGraph (prefixTick W) next ![prefixStartTerm c t q w r]))
    (child : D B Γ (programGraph (prefixLoop W) out ![fuel,next]))
    (unit : D B Γ (unary cellHead (suc z) out)) : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) := by
  let start := prefixStartTerm c t q w r
  have run := shiftLate (prefixTick W) start next fuel out first child
  exact exact_OpenPrefixOwnIntroduce W c t q w r out
    (headTransport (prefixLoop W) out (suc fuel) w ![start] (budget.map symm) run) unit

/-- A contextual lambda prefix with a certified first tick is accepted
when the actual child tape stops the prefix evaluator. The remaining
fuel uses the parent's own witness coordinate. -/
theorem exact_OpenContextualLambdaPrefixAfterStop (W : Program 3)
    (c t q w r c₁ t₁ q₁ w₁ r₁ fuel : OTerm α)
    (budget : D B Γ (eqn w (suc fuel)))
    (first : D B Γ (programGraph (prefixTick W) (prefixStartTerm c₁ t₁ q₁ w₁ r₁)
      ![prefixStartTerm c t q w r]))
    (stopped : D B Γ (programGraph isLambdaPrefix z ![c₁,t₁,q₁,w₁,r₁])) :
    D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) := by
  apply zeroSuccessorCases Γ fuel _
  · let E := eqn fuel z
    let next := prefixStartTerm c₁ t₁ q₁ w₁ r₁
    have zero : Derivation B (E :: Γ) E := Derivation.hypothesis List.mem_cons_self
    obtain ⟨length⟩ := budget
    obtain ⟨tick⟩ := first
    exact finishParent W c t q w r z next next
      ⟨trans (addHyp length E) (congSuc zero)⟩ ⟨addHyp tick E⟩
      (repeatZeroValue (prefixTick W) next) (headRead (suc z) (prefixFrameTerm c₁ t₁ q₁ w₁ r₁))
  · intro β j Δ n keep more
    simp only [bit5,programRename,fiveInputsRename,sucRelabel,zRelabel]
    have length := renameInto budget j Δ keep
    rw [eqnRelabel,sucRelabel] at length
    obtain ⟨length⟩ := length
    obtain ⟨more⟩ := more
    have tick := renameInto first j Δ keep
    simp only [programRename,inputsRename,prefixStartTermRename] at tick
    have stop := renameInto (stopTick W c₁ t₁ q₁ w₁ r₁ stopped) j Δ keep
    simp only [programRename,inputsRename,prefixStartTermRename,stateRename,sucRelabel,zRelabel] at stop
    let next := prefixStartTerm (c₁.relabel j) (t₁.relabel j) (q₁.relabel j) (w₁.relabel j) (r₁.relabel j)
    let terminal : OTerm β := stateTerm (suc z) z
    have fixed : D B Δ (programGraph (prefixLoop W) terminal ![n,terminal]) :=
      exact_OpenTickIterationFixed (prefixTick W) terminal n (exact_OpenPrefixTickTerminal W (suc z))
    have child : D B Δ (programGraph (prefixLoop W) terminal ![suc n,next]) :=
      shiftLate (prefixTick W) next terminal n terminal stop fixed
    exact finishParent W (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)
      (suc n) next terminal ⟨trans length (congSuc more)⟩ tick child (headRead (suc z) z)

#print axioms exact_OpenContextualLambdaPrefixAfterStop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixParentStopProof
