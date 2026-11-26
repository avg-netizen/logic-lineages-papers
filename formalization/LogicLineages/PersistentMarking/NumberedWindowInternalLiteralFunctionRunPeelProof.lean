module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionRunPeelProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenChecks (exact_OpenLiftedTick)
open NumberedWindowInternalSparseRawRun (iterateState ownState ownRun)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm ownLoop loopOwn)
open NumberedWindowInternalSparseRawRunShiftProof (shiftEarly shiftLate)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal terminalOwnRun)

/-- The literal predecessor of the actual tag-five witness code. This is
the parent's remaining fuel after one tick, not the child's fuel. -/
def functionRemaining {α : Type} (child : OTerm α) : OTerm α :=
  pairTerm (SourceComputabilityFormulaSupportProof.numeral 5) (rawCons child z)

abbrev parentTape {α : Type} (dom cod arg source child dest : OTerm α) : Fin 3 → OTerm α :=
  ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg]

abbrev childTape {α : Type} (source child dest : OTerm α) : Fin 3 → OTerm α :=
  ![source,child,dest]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- No fuel, shape or typing premise: the actual parent own state is the
same arbitrary output state as the actual child loop on the parent's
remaining fuel. Both directions use the same physical first tick. -/
theorem peelState (p other : Program 3) (dom cod arg source child dst out : OTerm α) :
    (Nonempty (Derivation body Γ
      (programGraph (ownState p other) out (parentTape dom cod arg source child dst))) →
      Nonempty (Derivation body Γ (programGraph (iterateState p other) out
        ![functionRemaining child,initialTerm (childTape source child dst)]))) ∧
    (Nonempty (Derivation body Γ (programGraph (iterateState p other) out
        ![functionRemaining child,initialTerm (childTape source child dst)])) →
      Nonempty (Derivation body Γ
        (programGraph (ownState p other) out (parentTape dom cod arg source child dst)))) := by
  let xs := parentTape dom cod arg source child dst
  let ys := childTape source child dst
  obtain ⟨d⟩ := exact_OpenLiftedTick body p other α z dom cod arg source child dst
  have tick : Nonempty (Derivation body Γ (programGraph
      (NumberedWindowInternalSparseRawTick.chosenTick p other) (initialTerm ys) ![initialTerm xs])) :=
    ⟨weakenClosed d Γ⟩
  constructor
  · intro hp
    exact shiftEarly p other (initialTerm xs) (initialTerm ys) (functionRemaining child) out
      tick (ownLoop p other out xs hp)
  · intro hc
    exact loopOwn p other out xs
      (shiftLate p other (initialTerm xs) (initialTerm ys) (functionRemaining child) out tick hc)

/-- A successor own-run flag on the literal function application lifts
and peels at exactly the child's remaining-fuel terminal state, inside
the original object calculus. It does not assert the smaller child's
own-code fuel suffices. -/
theorem exact_OpenFunctionRemainingFuel (body : Positive (Fin 1)) (p other : Program 3)
    (α : Type) (dom cod arg source child dst k : OTerm α) :
    let xs := parentTape dom cod arg source child dst
    let ys := childTape source child dst
    let run := programGraph (ownRun p other) (suc k) xs
    let terminal := programGraph (iterateState p other) (stateTerm (suc k) z)
      ![functionRemaining child,initialTerm ys]
    Nonempty (Derivation body [] ((run.imp terminal) ⊓ (terminal.imp run))) := by
  let xs := parentTape dom cod arg source child dst
  let ys := childTape source child dst
  let out := stateTerm (suc k) z
  let run := programGraph (ownRun p other) (suc k) xs
  let terminal := programGraph (iterateState p other) out
    ![functionRemaining child,initialTerm ys]
  have peel := peelState (body := body) (Γ := [run]) p other dom cod arg source child dst out
  obtain ⟨toChild⟩ := peel.1 (ownRunTerminal p other k xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have unpeel := peelState (body := body) (Γ := [terminal]) p other dom cod arg source child dst out
  obtain ⟨toParent⟩ := terminalOwnRun p other k xs
    (unpeel.2 ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction toChild) (Derivation.implicationIntroduction toParent)⟩

#print axioms exact_OpenFunctionRemainingFuel
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionRunPeelProof
