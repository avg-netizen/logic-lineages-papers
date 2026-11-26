module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingFirstTickProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelArithmeticProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelInductionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename addRelabel)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawRun (iterateState ownRun)
open NumberedWindowInternalSparseRawRunShiftProof (shiftEarly)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm ownRunLift)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickRename)
open NumberedWindowInternalLiteralDescendingFirstTickProof
  (FrameDecoder fallbackDecoder exact_OpenDescendingFirstTickWith)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralExcessTerminalProof
  (LitRun TerminalOne runRename exact_OpenTerminalFirstTickFromFuel)
open NumberedWindowInternalLiteralFuelArithmeticProof (expandExcess exact_OpenRootOwnFromExcess)
open NumberedWindowInternalLiteralFuelMotiveSyntaxProof (Row Measure Smaller smallerRename)
open NumberedWindowInternalLiteralFuelMotiveBindingProof (measureIntro measureAt smallerAt strongMeasure)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveRun {β : Type} (p other : Program 3) (q w r k : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (h : D B Γ (LitRun p other TerminalOne (add w k) q w r)) :
    D B Δ (LitRun p other TerminalOne (add (w.relabel j) (k.relabel j))
      (q.relabel j) (w.relabel j) (r.relabel j)) := by
  have moved := renameInto h j Δ keep
  rw [runRename,stateRename,sucRelabel,zRelabel,addRelabel] at moved
  exact moved

private theorem childOwn (p other : Program 3)
    (q w r k x v y : OTerm α)
    (ih : D B Γ (Smaller p other w))
    (lt : D B Γ (ltF v w))
    (tick : D B Γ (TickAt p other z (frameValueTerm x v y) q w r))
    (held : D B Γ (LitRun p other TerminalOne (add w k) q w r)) :
    D B Γ (bit (ownRun p other) ![q,w,r]) := by
  let goal := bit (ownRun p other) ![q,w,r]
  apply orderCases Γ v w goal lt
  intro β j Δ gap keep difference
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  let ys : Fin 3 → OTerm β := ![x.relabel j,v.relabel j,y.relabel j]
  let extra := add gap (k.relabel j)
  let out : OTerm β := TerminalOne
  have pos := expandExcess (w.relabel j) (v.relabel j) gap (k.relabel j) difference
  have h := moveRun p other q w r k j Δ keep held
  have late : D B Δ (LitRun p other out (suc (add (v.relabel j) extra))
      (q.relabel j) (w.relabel j) (r.relabel j)) :=
    headTransport (iterateState p other) out (add (w.relabel j) (k.relabel j))
      (suc (add (v.relabel j) extra)) ![initialTerm xs] pos h
  have move := renameInto tick j Δ keep
  simp only [tickRename,zRelabel,frameValueTerm,sucRelabel,rawConsRename] at move
  have early := shiftEarly p other (initialTerm xs) (initialTerm ys)
    (add (v.relabel j) extra) out move late
  have temp := renameInto ih j Δ keep
  rw [smallerRename] at temp
  have less := renameInto lt j Δ keep
  rw [orderRename] at less
  have bound := smallerAt p other (w.relabel j) (v.relabel j) temp less
  obtain ⟨atChild⟩ := measureAt p other (x.relabel j) (v.relabel j) (y.relabel j) extra bound
  obtain ⟨ok⟩ := early
  have accepts : D B Δ (bit (ownRun p other) ys) :=
    ⟨Derivation.implicationElimination atChild ok⟩
  have result := ownRunLift p other z xs ys move less accepts
  simp only [goal,bit,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact result

/-- Strong induction over the exact original open witness code with
independent raw endpoints and independent extra fuel. Only terminal
flag one is trimmed; an arbitrary state or fabricated fallback is not. -/
theorem exact_OpenFuelMeasureWith (p F : Program 3) (decode : FrameDecoder F) (w : OTerm α) :
    D B Γ (Measure p F w) := by
  apply strongMeasure p F w
  intro β Δ v ih
  apply measureIntro p F v
  intro γ j Ω q r k keep
  let t := v.relabel j
  let A := LitRun p F TerminalOne (add t k) q t r
  let Ξ := A :: Ω
  let goal := bit (ownRun p F) ![q,t,r]
  have smaller := renameInto ih j Ξ (fun p hp => List.mem_cons_of_mem _ (keep p hp))
  rw [smallerRename] at smaller
  have accepts : D B Ξ A := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have done : D B Ξ goal := by
    apply exact_OpenDescendingFirstTickWith p F decode q t r goal
    · intro τ l Λ flag keep rootTag _ tick
      simp only [goal,bit,programRename,tripleInputsRename,sucRelabel,zRelabel]
      exact exact_OpenRootOwnFromExcess p F _ _ _ flag _ rootTag tick
        (moveRun p F q t r k l Λ keep accepts)
    · intro τ l Λ keep tick
      have accepted := moveRun p F q t r k l Λ keep accepts
      obtain ⟨wrong⟩ := exact_OpenTerminalFirstTickFromFuel p F _ _ _ z _ tick accepted
      exact ⟨Derivation.explosion (sucNeZeroApply (symm wrong))⟩
    · intro τ l Λ x child y keep lt tick
      have sub := renameInto smaller l Λ keep
      rw [smallerRename] at sub
      simp only [goal,bit,programRename,tripleInputsRename,sucRelabel,zRelabel]
      exact childOwn p F (q.relabel l) (t.relabel l) (r.relabel l) (k.relabel l) x child y
        sub lt tick (moveRun p F q t r k l Λ keep accepts)
  obtain ⟨d⟩ := done
  exact ⟨Derivation.implicationIntroduction d⟩

theorem exact_OpenFuelMeasure (p other : Program 3) (w : OTerm α) :
    D B Γ (Measure p (fallback other) w) :=
  exact_OpenFuelMeasureWith p (fallback other) (fallbackDecoder other) w

theorem exact_OpenTrimmedOwnRunWith (p F : Program 3) (decode : FrameDecoder F) (q w r k : OTerm α)
    (held : D B Γ (LitRun p F TerminalOne (add w k) q w r)) :
    D B Γ (bit (ownRun p F) ![q,w,r]) := by
  obtain ⟨rule⟩ := measureAt p F q w r k (exact_OpenFuelMeasureWith p F decode w)
  obtain ⟨d⟩ := held
  exact ⟨Derivation.implicationElimination rule d⟩

/-- The actual physically descending raw machine at its original own
witness accepts whenever it accepts with any extra fuel. -/
theorem exact_OpenTrimmedOwnRun (p other : Program 3) (q w r k : OTerm α)
    (held : D B Γ (LitRun p (fallback other) TerminalOne (add w k) q w r)) :
    D B Γ (bit (ownRun p (fallback other)) ![q,w,r]) :=
  exact_OpenTrimmedOwnRunWith p (fallback other) (fallbackDecoder other) q w r k held

#print axioms exact_OpenFuelMeasureWith
#print axioms exact_OpenTrimmedOwnRunWith
#print axioms exact_OpenFuelMeasure
#print axioms exact_OpenTrimmedOwnRun
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelInductionProof
