module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLiveRootSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChosenSuccessCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D exact_OpenLiveRootSuccess)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Invert a successful chosen tick with an arbitrary earlier state.
Either the actual zero-frame test retained that state, or all three
actual row selectors produce a tape accepted by the root callback.
The two continuations run in the same object body with explicit
context preservation. No syntactic shape of the earlier state is assumed. -/
theorem exact_OpenChosenSuccessCases (p other : Program 3) (start k f : OTerm α)
    (goal : Formula α)
    (known : D B Γ (programGraph (chosenTick p other) (stateTerm (suc k) f) ![start]))
    (terminal : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary stateFrame z (start.relabel j)) →
      D B Δ (eqn (start.relabel j) (stateTerm (suc (k.relabel j)) (f.relabel j))) →
      D B Δ (goal.relabel j))
    (live : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary stateFrame (suc frame) (start.relabel j)) →
      D B Δ (unary rowSource (tape 0) (start.relabel j)) →
      D B Δ (unary rowWitness (tape 1) (start.relabel j)) →
      D B Δ (unary rowDestination (tape 2) (start.relabel j)) →
      D B Δ (programGraph (rootCall p) (suc (k.relabel j)) tape) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply optionGraphCases stateFrame ![start] goal
  · intro β j Δ keep zero
    rw [inputsRename] at zero
    have held := renameInto known j Δ keep
    simp only [programRename,inputsRename,stateRename,sucRelabel] at held
    let st := start.relabel j
    let out := stateTerm (suc (k.relabel j)) (f.relabel j)
    have projected := zeroBranchElim stateFrame (.projection 0) (performLive p other) out ![st] zero held
    have same := valueUnique (.projection 0) st out ![st] (projectionValue 0 ![st]) projected
    exact terminal β j Δ keep zero same
  · intro β j Δ frame keep present
    rw [inputsRename] at present
    have held := renameInto known j Δ keep
    simp only [programRename,inputsRename,stateRename,sucRelabel] at held
    let st := start.relabel j
    let out := stateTerm (suc (k.relabel j)) (f.relabel j)
    have next := successorBranchElim stateFrame (.projection 0) (performLive p other)
      out frame ![st] present held
    apply programCompositionCases (liveTick p other) ![rowSource,rowWitness,rowDestination]
      out ![st] (goal.relabel j) next
    intro γ l tape Ω stay tick select
    let m := l ∘ j
    have retain (φ : Formula α) (hφ : φ ∈ Γ) : φ.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using stay _ (keep φ hφ)
    have frameAgain := renameInto present l Ω stay
    simp only [programRename,inputsRename,sucRelabel] at frameAgain
    simp only [out,stateRename,sucRelabel] at tick
    have root := exact_OpenLiveRootSuccess p other ((k.relabel j).relabel l)
      ((f.relabel j).relabel l) tape tick
    have q := select 0
    have w := select 1
    have r := select 2
    simp only [inputsRename,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.tail_cons,Matrix.head_cons] at q w r
    have reply := live γ m Ω (frame.relabel l) tape retain
      (by simpa only [m,st,unary,Term.relabel_relabel] using frameAgain)
      (by simpa only [m,st,unary,Term.relabel_relabel] using q)
      (by simpa only [m,st,unary,Term.relabel_relabel] using w)
      (by simpa only [m,st,unary,Term.relabel_relabel] using r)
      (by simpa only [m,Term.relabel_relabel] using root)
    simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenChosenSuccessCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChosenSuccessCasesProof
