module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue outputTransport)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame emitFrame frameGood frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTick (tagFiveTest rootTest rootCall)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D)
open NumberedWindowInternalLiteralAuxFirstTickCasesProof (TickAt exact_OpenAuxiliaryFirstTickCases)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit nodeAtCases)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts exact_OpenFunctionGuardParts)
open NumberedWindowInternalLiteralRunTerminalFlagProof (exact_OpenTerminalFirstTickFlag)
open NumberedWindowInternalLiteralAuxRunChildProof
  (ChildTerminal functionTick exact_OpenAuxiliaryRemainingChild)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rejectTerminal (p other : Program 3) (q w r : OTerm α) (goal : Formula α)
    (tick : D B Γ (TickAt p other z z q w r))
    (success : D B Γ (bit (ownRun p (auxiliaryFallback other)) ![q,w,r])) : D B Γ goal := by
  obtain ⟨zeroOne⟩ := exact_OpenTerminalFirstTickFlag p (auxiliaryFallback other) q w r z tick success
  exact ⟨Derivation.explosion (sucNeZeroApply (symm zeroOne))⟩

private theorem functionSuccess (p other : Program 3) (q w r : OTerm α)
    (five : D B Γ (bit tagFiveTest ![q,w,r]))
    (success : D B Γ (bit (ownRun p (auxiliaryFallback other)) ![q,w,r])) :
    D B Γ (bit frameGood ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let g := bit frameGood xs
  obtain ⟨h⟩ := success
  obtain ⟨t⟩ := five
  have no : D B (g.not :: Γ) g := by
    have nz : D B (g.not :: Γ) g.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero : D B (g.not :: Γ) (programGraph frameGood z xs) := by
      unfold frameGood
      exact conjunctionReject _ _ xs nz
    have bad := zeroBranchIntro frameGood (constantZero 3) emitFrame z xs zero (constantZeroValue xs)
    exact rejectTerminal p other q w r g (functionTick p other q w r z ⟨addHyp t _⟩ bad) ⟨addHyp h _⟩
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle g)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction no)⟩

/-- Invert an actual accepting check from an auxiliary application
source. Roots expose the actual raw payload graph, not a recomputed
step; non-roots expose a matching function context, its unchanged raw
argument, and the original terminal loop on its exact remaining fuel. -/
theorem exact_OpenAuxiliaryRunInversion (p other : Program 3) (q w r : OTerm α)
    (goal : Formula α) (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (accepts : D B Γ (bit (ownRun p (auxiliaryFallback other)) ![q,w,r]))
    (root : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) → D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
      D B Δ (bit p ![q.relabel j,payload,r.relabel j]) → D B Δ (goal.relabel j))
    (context : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg child dom' cod' dest arg' : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
        dom cod fn arg child dom' cod' dest arg' →
      D B Δ (ChildTerminal p other fn child dest) → D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenAuxiliaryFirstTickCases p other q w r goal aux
  · intro β j Δ frame keep five _ _
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    have yes := moveBit _ q w r j Δ keep accepts
    have good := functionSuccess p other q' w' r' five yes
    apply exact_OpenFunctionGuardParts q' w' r' (goal.relabel j) good
    intro γ k Ω dom cod fn arg child dom' cod' dest arg' stay fields
    have terminal := exact_OpenAuxiliaryRemainingChild p other (q'.relabel k) (w'.relabel k) (r'.relabel k)
      dom cod fn arg child dom' cod' dest arg'
      (moveBit _ q' w' r' k Ω stay five) fields (moveBit _ q' w' r' k Ω stay yes)
    have all (f : Formula α) (h : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
      simpa only [formulaRelabelComposition] using stay _ (keep f h)
    have rest := context γ (k ∘ j) Ω dom cod fn arg child dom' cod' dest arg' all
      (by simpa only [q',w',r',Term.relabel_relabel] using fields) terminal
    simpa only [formulaRelabelComposition] using rest
  · intro β j Δ flag keep test call tick
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    let xs : Fin 3 → OTerm β := ![q',w',r']
    have yes := moveBit _ q w r j Δ keep accepts
    have unit := exact_OpenTerminalFirstTickFlag p (auxiliaryFallback other) q' w' r' flag tick yes
    have chosen : D B Δ (bit (rootCall p) xs) :=
      outputTransport (rootCall p) flag (suc z) xs unit call
    apply nodeAtCases 0 1 1 xs (goal.relabel j) test
    intro γ k Ω values stay size eq reports
    rcases values with _ | ⟨payload,_ | ⟨unexpected,rest⟩⟩
    · simp at size
    · let ys : Fin 3 → OTerm γ := ![q'.relabel k,w'.relabel k,r'.relabel k]
      have chk := moveBit (rootCall p) q' w' r' k Ω stay chosen
      have h := normalizeRecover (.composition p ![.projection 0,frameSlot 0 1,.projection 2]) ys chk
      have actual : D B Ω (bit p ![q'.relabel k,payload,r'.relabel k]) := by
        apply compositionRecover p ![.projection 0,frameSlot 0 1,.projection 2] (suc z)
          ys ![q'.relabel k,payload,r'.relabel k] h
        intro i
        exact Fin.cases (projectionValue 0 ys)
          (Fin.cases (onTape (field 0) 1 payload ys reports.1)
            (Fin.cases (projectionValue 2 ys) (fun e => Fin.elim0 e))) i
      have all (f : Formula α) (h : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
        simpa only [formulaRelabelComposition] using stay _ (keep f h)
      have shaped : D B Ω (eqn ((w'.relabel k)) (rootWitnessTerm payload)) := eq
      have part := root γ (k ∘ j) Ω payload all
        (by simpa only [w',Term.relabel_relabel] using shaped)
        (by simpa only [q',r',Term.relabel_relabel] using actual)
      simpa only [formulaRelabelComposition] using part
    · simp at size
  · intro Δ keep rejected
    have yes := accepts.map (Derivation.weakening (fun f h => keep f h))
    exact rejectTerminal p other q w r goal rejected yes

#print axioms exact_OpenAuxiliaryRunInversion
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunInversionProof
