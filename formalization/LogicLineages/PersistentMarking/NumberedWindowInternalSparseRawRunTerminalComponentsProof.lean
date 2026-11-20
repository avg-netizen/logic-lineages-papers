module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalComponentsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue recursionZeroValue)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawRun (iterateState step)

abbrev loopArgs {α : Type} (fuel st : OTerm α) : Fin 2 → OTerm α := ![fuel,st]

abbrev loopGraph {α : Type} (p other : Program 3) (st fuel : OTerm α) : Formula α :=
  programGraph (iterateState p other) st (loopArgs fuel st)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem zeroLoopGraph (p other : Program 3) (st : OTerm α) :
    Nonempty (Derivation body Γ (loopGraph p other st z)) :=
  recursionZeroValue (.projection 0) (step p other) st ![st] (projectionValue 0 ![st])

theorem nextLoopGraph (p other : Program 3) (st fuel : OTerm α)
    (prior : Nonempty (Derivation body Γ (loopGraph p other st fuel)))
    (fixed : Nonempty (Derivation body Γ (programGraph (chosenTick p other) st ![st]))) :
    Nonempty (Derivation body Γ (loopGraph p other st (suc fuel))) := by
  let xs : Fin 3 → OTerm α := ![fuel,st,st]
  let ys : Fin 1 → OTerm α := ![st]
  let selectPrior : Fin 1 → Program 3 := fun _ => .projection 1
  have computed : Nonempty (Derivation body Γ (programGraph (step p other) st xs)) := by
    apply compositionValue (chosenTick p other) selectPrior st xs ys fixed
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact recursionSuccessorIntroduction (n := 1) Γ (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula (step p other)) st fuel st ![st] prior computed

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalComponentsProof
