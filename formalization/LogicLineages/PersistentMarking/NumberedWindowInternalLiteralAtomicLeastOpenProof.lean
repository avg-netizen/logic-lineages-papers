module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename projectionValue valueUnique compositionValue outputTransport)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalLiteralAtomicLeastGuardProof
  (guardedLeast atomOutput checkAtom keepAtom checkSame outRaw pairSecond)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (φ : Formula α) :=
  Nonempty (Derivation B Γ φ)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

theorem outReport (q t : OTerm α) : D B Γ (programGraph outRaw t ![q,suc t]) := by
  unfold outRaw pairSecond
  apply compositionValue predOne (Fin.cons (.projection 1) Fin.elim0) t ![q,suc t] ![suc t]
    (by rw [exact_DispatchControlAST.2.2.1]; exact predecessorSuccessor t)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![q,suc t]

theorem rejectZeroOutput (xs : Fin 2 → OTerm α) (t : OTerm α) (goal : Formula α)
    (bad : D B Γ (programGraph (constantZero 2) (suc t) xs)) : D B Γ goal := by
  obtain ⟨contradiction⟩ := valueUnique (constantZero 2) (suc t) z xs bad (constantZeroValue xs)
  exact ⟨Derivation.explosion (sucNeZeroApply contradiction)⟩

/-- Any successful outer gate reports precisely the input's actual
selected code, never a replacement for it. -/
theorem outputIsSelected (q coded t : OTerm α)
    (h : D B Γ (programGraph atomOutput (suc t) ![q,coded])) :
    D B Γ (eqn coded (suc t)) := by
  apply optionGraphCases checkAtom ![q,coded] (eqn coded (suc t))
  · intro β j Δ keep zero
    rw [eqnRelabel,sucRelabel]
    rw [pairRename] at zero
    let xs : Fin 2 → OTerm β := ![q.relabel j,coded.relabel j]
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    have yes := zeroBranchElim checkAtom (.projection 1) keepAtom (suc (t.relabel j)) xs zero held
    exact valueUnique (.projection 1) (coded.relabel j) (suc (t.relabel j)) xs
      (projectionValue 1 xs) yes
  · intro β j Δ k keep atom
    rw [eqnRelabel,sucRelabel]
    rw [pairRename] at atom
    let xs : Fin 2 → OTerm β := ![q.relabel j,coded.relabel j]
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    have kept := successorBranchElim checkAtom (.projection 1) keepAtom (suc (t.relabel j)) k xs atom held
    apply optionGraphCases checkSame xs (eqn (coded.relabel j) (suc (t.relabel j)))
    · intro γ l Ω stay zero
      have current := renameInto kept l Ω stay
      simp only [programRename,xs,pairRename,sucRelabel] at current
      simp only [xs,pairRename] at zero
      exact rejectZeroOutput _ _ _
        (zeroBranchElim checkSame (constantZero 2) (.projection 1) _ _ zero current)
    · intro γ l Ω pred stay eq
      rw [eqnRelabel,sucRelabel]
      have current := renameInto kept l Ω stay
      simp only [programRename,xs,pairRename,sucRelabel] at current
      simp only [xs,pairRename] at eq
      have yes := successorBranchElim checkSame (constantZero 2) (.projection 1) _ pred _ eq current
      let args : Fin 2 → OTerm γ := ![(q.relabel j).relabel l,(coded.relabel j).relabel l]
      exact valueUnique (.projection 1) ((coded.relabel j).relabel l) (suc ((t.relabel j).relabel l))
        args (projectionValue 1 args) yes

/-- The literal guarded least graph yields both the original successful
least graph and the actual gate on exactly that original input and
successor output. All equalities are internal to the current body. -/
theorem exact_OpenAtomicLeastReport (L : Program 3) (ctx ty q t : OTerm α)
    (h : D B Γ (programGraph (guardedLeast L) (suc t) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc t) ![ctx,ty,q] ⊓ programGraph atomOutput (suc t) ![q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let fs : Fin 2 → Program 3 := Fin.cons (.projection 2) (Fin.cons L Fin.elim0)
  have underlying : D B Γ (programGraph L (suc t) xs) := by
    apply programCases L xs (programGraph L (suc t) xs)
    intro β j Δ actual keep held
    simp only [xs,tripleInputsRename] at held
    simp only [xs,programRename,tripleInputsRename,sucRelabel]
    let xj : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,q.relabel j]
    have h' := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at h'
    have gate : D B Δ (programGraph atomOutput (suc (t.relabel j)) ![q.relabel j,actual]) := by
      apply compositionRecover atomOutput fs (suc (t.relabel j)) xj ![q.relabel j,actual] h'
      intro k
      exact Fin.cases (projectionValue 2 xj) (Fin.cases held (fun r => Fin.elim0 r)) k
    exact outputTransport L actual (suc (t.relabel j)) xj
      (outputIsSelected (q.relabel j) actual (t.relabel j) gate) held
  have gate : D B Γ (programGraph atomOutput (suc t) ![q,suc t]) := by
    apply compositionRecover atomOutput fs (suc t) xs ![q,suc t] h
    intro k
    exact Fin.cases (projectionValue 2 xs) (Fin.cases underlying (fun r => Fin.elim0 r)) k
  obtain ⟨u⟩ := underlying
  obtain ⟨g⟩ := gate
  exact ⟨Derivation.conjunctionIntroduction u g⟩

#print axioms outReport
#print axioms outputIsSelected
#print axioms exact_OpenAtomicLeastReport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
