module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFold (iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop loopArgs)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalNilLoop)
open NumberedWindowInternalSparsePositiveTerminalityTargets (terminalScratch)
open NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof (terminalRename supplyTerminal)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)

attribute [local irreducible] programGraph iterateState

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem samePair (raw : Program 5) (least : Program 3)
    (out state fuel ctx ty current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out fuel ctx ty current z)))
    (seed : Nonempty (Derivation body Γ (scratchGraph state z current))) :
    Nonempty (Derivation body Γ (scratchGraph out z current)) := by
  have stays := closedApply (exact_OpenTerminalNilLoop body raw least α state fuel ctx ty current) seed
  have e := valueUnique (iterateState raw least) state out (loopArgs fuel ctx ty current z) stays loop
  exact outputTransport consCode state out (![z,current] : Fin 2 → OTerm α) e seed

theorem fromNil (raw : Program 5) (least : Program 3) (out fuel ctx ty current : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out fuel ctx ty current z))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  apply scratchCases z current (terminalScratch out)
  intro β j Δ state hJ seed
  rw [terminalRename]
  rw [zRelabel] at seed
  have given := moveLoop j Δ hJ raw least out fuel ctx ty current z loop
  rw [zRelabel] at given
  exact supplyTerminal (out.relabel j) (current.relabel j)
    (samePair raw least (out.relabel j) state (fuel.relabel j) (ctx.relabel j)
      (ty.relabel j) (current.relabel j) given seed)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityNilProof
