module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)
open NumberedWindowInternalLiteralAuxFallback
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D shapeReject initialTick)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev TickAt (p other : Program 3) (flag frame q w r : OTerm α) : Formula α :=
  programGraph (chosenTick p (auxiliaryFallback other)) (stateTerm flag frame)
    ![initialTerm (![q,w,r])]

private theorem moveZero {β : Type} (p : Program 3) (q w r : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (h : D B Γ (programGraph p z ![q,w,r])) :
    D B Δ (programGraph p z ![q.relabel j,w.relabel j,r.relabel j]) := by
  have out := renameInto h j Δ keep
  simpa only [programRename,tripleInputsRename,zRelabel] using out

/-- On an exact auxiliary source, this executable tick has only three
possible branches. Function and root branches expose their originals'
actual output graph. The rejection branch has no arbitrary callback. -/
theorem exact_OpenAuxiliaryFirstTickCases (p other : Program 3) (q w r : OTerm α)
    (goal : Formula α) (source : D B Γ (bit sourceIsAux ![q,w,r]))
    (functionCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (frame : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit tagFiveTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (programGraph chosenFrame frame ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (TickAt p other z frame (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (rootCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (flag : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (programGraph (rootCall p) flag ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (TickAt p other flag z (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (rejectedCase : ∀ (Δ : List (Formula α)), (∀ f ∈ Γ, f ∈ Δ) →
      D B Δ (TickAt p other z z q w r) → D B Δ goal) :
    D B Γ goal := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let F := auxiliaryFallback other
  let Bad := emitState (constantZero 3) F
  let Root := emitState (rootCall p) (constantZero 3)
  let Fn := emitState (constantZero 3) chosenFrame
  let P := bit tagFiveTest xs
  let R := bit rootTest xs
  have yes : D B (P :: Γ) goal := by
    have yesFive : D B (P :: Γ) P := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply programCases chosenFrame xs goal
    intro β j Δ frame keep call
    let vs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
    have ok := moveBit tagFiveTest q w r j Δ keep yesFive
    have call' : D B Δ (programGraph chosenFrame frame vs) := by
      simpa only [xs,tripleInputsRename] using call
    have run := successorBranchIntro tagFiveTest (branch rootTest Bad Root) Fn
      (stateTerm z frame) z vs ok (emitGraph _ _ z frame vs (constantZeroValue vs) call')
    exact functionCase β j Δ frame (fun f h => keep f (List.mem_cons_of_mem _ h))
      ok call' (initialTick p F _ _ _ _ run)
  have no : D B (P.not :: Γ) goal := by
    have zeroFive : D B (P.not :: Γ) (programGraph tagFiveTest z xs) :=
      shapeReject _ _ 1 xs ⟨Derivation.hypothesis List.mem_cons_self⟩
    have rooted : D B (R :: P.not :: Γ) goal := by
      have yesRoot : D B (R :: P.not :: Γ) R := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply programCases (rootCall p) xs goal
      intro β j Δ flag keep call
      let vs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
      have zero := moveZero tagFiveTest q w r j Δ (fun f h => keep f (List.mem_cons_of_mem _ h)) zeroFive
      have ok := moveBit rootTest q w r j Δ keep yesRoot
      have call' : D B Δ (programGraph (rootCall p) flag vs) := by
        simpa only [xs,tripleInputsRename] using call
      have base := successorBranchIntro rootTest Bad Root (stateTerm flag z) z vs ok
        (emitGraph _ _ flag z vs call' (constantZeroValue vs))
      have run := zeroBranchIntro tagFiveTest (branch rootTest Bad Root) Fn
        (stateTerm flag z) vs zero base
      exact rootCase β j Δ flag (fun f h => keep f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
        ok call' (initialTick p F _ _ _ _ run)
    have rejected : D B (R.not :: P.not :: Γ) goal := by
      let Δ := R.not :: P.not :: Γ
      have rootZero : D B Δ (programGraph rootTest z xs) :=
        shapeReject _ _ 1 xs ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨fz⟩ := zeroFive
      have fiveZero : D B Δ (programGraph tagFiveTest z xs) := ⟨addHyp fz _⟩
      obtain ⟨test⟩ := source
      have auxOne : D B Δ (bit sourceIsAux xs) := ⟨addHyp (addHyp test _) _⟩
      have inner := zeroBranchIntro tagFiveTest (constantZero 3) chosenFrame z xs fiveZero
        (constantZeroValue xs)
      have v := successorBranchIntro sourceIsAux other (branch tagFiveTest (constantZero 3) chosenFrame)
        z z xs auxOne inner
      have bad := emitGraph (constantZero 3) F z z xs (constantZeroValue xs) v
      have base := zeroBranchIntro rootTest Bad Root (stateTerm z z) xs rootZero bad
      have run := zeroBranchIntro tagFiveTest (branch rootTest Bad Root) Fn (stateTerm z z) xs fiveZero base
      exact rejectedCase Δ (fun f h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        (initialTick p F q w r _ run)
    obtain ⟨r⟩ := rooted
    obtain ⟨n⟩ := rejected
    exact ⟨disjunctionElimination (excludedMiddle R)
      (Derivation.implicationIntroduction r) (Derivation.implicationIntroduction n)⟩
  obtain ⟨y⟩ := yes
  obtain ⟨n⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction y) (Derivation.implicationIntroduction n)⟩

#print axioms exact_OpenAuxiliaryFirstTickCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickCasesProof
