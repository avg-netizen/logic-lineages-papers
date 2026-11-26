module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingTickSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExcessTerminalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (headTransport recursionZeroValue projectionValue programRename valueUnique zeroSuccessorCases)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalSparseRawRunTerminalChecks (exact_OpenRawTerminalLoop)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalSparseRawRunShiftProof (shiftLate)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)
open NumberedWindowInternalLiteralRunTerminalFlagProof (starterRename)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickRename)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev TerminalOne {α : Type} : OTerm α := stateTerm (suc z) z

abbrev LitRun (p other : Program 3) (out fuel q w r : OTerm α) : Formula α :=
  programGraph (iterateState p other) out ![fuel,initialTerm (![q,w,r])]

theorem runRename {β : Type} (p other : Program 3) (o f q w r : OTerm α) (j : α → β) :
    (LitRun p other o f q w r).relabel j =
      LitRun p other (o.relabel j) (f.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  unfold LitRun
  rw [programRename]
  have inp : (fun i : Fin 2 => ((![f,initialTerm (![q,w,r])] : Fin 2 → OTerm α) i).relabel j) =
      ![f.relabel j,initialTerm (![q.relabel j,w.relabel j,r.relabel j])] := by
    funext i
    exact Fin.cases rfl (Fin.cases (starterRename q w r j) (fun k => Fin.elim0 k)) i
  rw [inp]

theorem flagAtEqualStates (a b f g : OTerm α)
    (h : D B Γ (eqn (stateTerm a f) (stateTerm b g))) :
    D B Γ (eqn a b) := by
  have before := headRead (body := B) (Γ := Γ) a f
  have after := headTransport cellHead a (stateTerm a f) (stateTerm b g) Fin.elim0 h before
  exact valueUnique cellHead a b ![stateTerm b g] after (headRead b g)

/-- Zero fuel cannot produce the unit terminal state from a fresh raw
tape. Its initial scratch has the actual stored zero flag. -/
theorem exact_OpenNoSuccessAtZeroFuel (p other : Program 3) (q w r : OTerm α)
    (held : D B Γ (LitRun p other TerminalOne z q w r)) : D B Γ (⊥ : Formula α) := by
  let start := initialTerm (![q,w,r])
  have base : D B Γ (LitRun p other start z q w r) :=
    recursionZeroValue (.projection 0) (step p other) start ![start] (projectionValue 0 ![start])
  have eq : D B Γ (eqn start TerminalOne) :=
    valueUnique (iterateState p other) start TerminalOne ![z,start] base held
  obtain ⟨bad⟩ := flagAtEqualStates z (suc z) (frameValueTerm q w r) z eq
  exact ⟨sucNeZeroApply (symm bad)⟩

/-- A unit terminal result at any supplied fuel identifies the exact
first tick's terminal flag. This is not restricted to a witness-own run. -/
theorem exact_OpenTerminalFirstTickFromFuel (p other : Program 3) (q w r flag fuel : OTerm α)
    (first : D B Γ (TickAt p other flag z q w r))
    (held : D B Γ (LitRun p other TerminalOne fuel q w r)) :
    D B Γ (eqn flag (suc z)) := by
  apply zeroSuccessorCases Γ fuel (eqn flag (suc z))
  · let Δ := eqn fuel z :: Γ
    obtain ⟨h⟩ := held
    have moved : D B Δ (LitRun p other TerminalOne z q w r) :=
      headTransport (iterateState p other) TerminalOne fuel z ![initialTerm (![q,w,r])]
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp h _⟩
    exact (exact_OpenNoSuccessAtZeroFuel p other q w r moved).map Derivation.explosion
  · intro β j Δ n keep fEq
    rw [eqnRelabel,sucRelabel,zRelabel]
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    let c := flag.relabel j
    let before := initialTerm (![q',w',r'])
    let after := stateTerm c z
    have t := renameInto first j Δ keep
    rw [tickRename,zRelabel] at t
    obtain ⟨tail⟩ := exact_OpenRawTerminalLoop B p other β c n
    have value := shiftLate p other before after n after t ⟨weakenClosed tail Δ⟩
    have moved := renameInto held j Δ keep
    simp only [runRename,stateRename,sucRelabel,zRelabel] at moved
    have forced := headTransport (iterateState p other) TerminalOne (fuel.relabel j) (suc n)
      ![before] fEq moved
    have eq := valueUnique (iterateState p other) after TerminalOne ![suc n,before] value forced
    exact flagAtEqualStates c (suc z) z z eq

#print axioms exact_OpenNoSuccessAtZeroFuel
#print axioms exact_OpenTerminalFirstTickFromFuel
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExcessTerminalProof
