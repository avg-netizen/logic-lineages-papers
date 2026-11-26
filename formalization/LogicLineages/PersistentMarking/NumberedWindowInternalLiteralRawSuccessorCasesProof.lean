module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChosenSuccessCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorEliminationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessorCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraph (recursion)
open ID1Completion.InternalRecursionGraphSuccessorEliminationProof
  (actualOriginalRecursionSuccessorElimination)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply successorCases)
open ID1Completion.InternalControlGraphSupportProof (projectionValue programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick
  (chosenTick rootCall stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalLiteralChosenSuccessCasesProof (exact_OpenChosenSuccessCases)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Peel one successor from the actual raw-run fuel. The previous
scratch is an object eigenvariable at the very same start, not a
numerically recomputed term. The exposed step is the genuine chosen
tick, with the machine's unused fuel and start arguments removed. -/
theorem exact_OpenLiteralRawSuccessorCases (p other : Program 3) (fuel start out : OTerm α)
    (goal : Formula α)
    (held : D B Γ (programGraph (iterateState p other) out ![suc fuel,start]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (prev : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev ![fuel.relabel j,start.relabel j]) →
      D B Δ (programGraph (chosenTick p other) (out.relabel j) ![prev]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let f := OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1))
  let g := OrdinaryArithmetic.graphFormula (step p other)
  have run : D B Γ (recursion f g out (suc fuel) ![start]) := held
  have calls := closedApply
    (actualOriginalRecursionSuccessorElimination B 1 α f g out fuel ![start]) run
  apply successorCases Γ f g out fuel ![start] goal calls
  intro β j Δ prev keep prior slot
  rw [inputsRename] at prior slot
  let xs : Fin 3 → OTerm β := ![fuel.relabel j,prev,start.relabel j]
  have exactSlot : D B Δ (programGraph (step p other) (out.relabel j) xs) := slot
  have tick : D B Δ (programGraph (chosenTick p other) (out.relabel j) ![prev]) := by
    apply compositionRecover (chosenTick p other) (fun _ : Fin 1 => .projection 1)
      (out.relabel j) xs ![prev] exactSlot
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact use β j Δ prev keep prior tick

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

/-- A nonzero flag at successor fuel was either already present at the
same output at predecessor fuel, or it comes from a live root call on
the preceding scratch's actual three decoded tape coordinates. This
is the single-step alternative for induction on an open fuel term. -/
theorem exact_OpenLiteralRawSuccessorSuccessCases (p other : Program 3)
    (fuel start k f : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (iterateState p other) (stateTerm (suc k) f) ![suc fuel,start]))
    (earlier : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) (stateTerm (suc (k.relabel j)) (f.relabel j))
        ![fuel.relabel j,start.relabel j]) →
      D B Δ (goal.relabel j))
    (rooted : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (prev frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev ![fuel.relabel j,start.relabel j]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (rootCall p) (suc (k.relabel j)) tape) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply exact_OpenLiteralRawSuccessorCases p other fuel start (stateTerm (suc k) f) goal held
  intro β j Δ prev keep prior tick
  rw [stateRename,sucRelabel] at tick
  apply exact_OpenChosenSuccessCases p other prev (k.relabel j) (f.relabel j) (goal.relabel j) tick
  · intro γ l Ω stay _ same
    let m := l ∘ j
    have retain (φ : Formula α) (hφ : φ ∈ Γ) : φ.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using stay _ (keep φ hφ)
    have run := renameInto prior l Ω stay
    simp only [programRename,pairRename] at run
    have ret := outputTransport (iterateState p other) (prev.relabel l)
      (stateTerm (suc ((k.relabel j).relabel l)) ((f.relabel j).relabel l))
      ![(fuel.relabel j).relabel l,(start.relabel j).relabel l] same run
    have reply := earlier γ m Ω retain (by simpa only [m,Term.relabel_relabel] using ret)
    simpa only [m,formulaRelabelComposition] using reply
  · intro γ l Ω frame tape stay live left cert right hit
    let m := l ∘ j
    have retain (φ : Formula α) (hφ : φ ∈ Γ) : φ.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using stay _ (keep φ hφ)
    have run := renameInto prior l Ω stay
    simp only [programRename,pairRename] at run
    have reply := rooted γ m Ω (prev.relabel l) frame tape retain
      (by simpa only [m,Term.relabel_relabel] using run) live left cert right
      (by simpa only [m,Term.relabel_relabel] using hit)
    simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenLiteralRawSuccessorCases
#print axioms exact_OpenLiteralRawSuccessorSuccessCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessorCasesProof
