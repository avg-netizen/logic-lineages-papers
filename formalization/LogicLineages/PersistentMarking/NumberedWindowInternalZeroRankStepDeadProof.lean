module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvance
import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepDeadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode tailCode)
open ID1Completion.InternalRawListRecursionSupportProof (consTail)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalControlGraphSupportProof (emptyRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePositiveFold (scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankStepTransportProof
open NumberedWindowInternalZeroRankAdvanceOpenProof (exact_OpenFilteredAdvanceDead)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem goodUpdate (A : Program 4) (xs : Fin 6 → OTerm α) (cur mark out : OTerm α)
    (liveCursor : Report (B := B) (Γ := Γ) scratchCursor (suc cur) xs)
    (goodCell : Report (B := B) (Γ := Γ) (onCursor cellGood) (suc mark) xs)
    (held : Report (B := B) (Γ := Γ) (stepAt A) out xs) :
    Report (B := B) (Γ := Γ) (updateAt A) out xs := by
  have inside := successorBranchElim scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out cur xs liveCursor held
  exact successorBranchElim (onCursor cellGood) dead (updateAt A) out mark xs goodCell inside

theorem badOutput (A : Program 4) (xs : Fin 6 → OTerm α) (cur out : OTerm α)
    (liveCursor : Report (B := B) (Γ := Γ) scratchCursor (suc cur) xs)
    (badCell : Report (B := B) (Γ := Γ) (onCursor cellGood) z xs)
    (held : Report (B := B) (Γ := Γ) (stepAt A) out xs) :
    Report (B := B) (Γ := Γ) dead out xs := by
  have inside := successorBranchElim scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out cur xs liveCursor held
  exact zeroBranchElim (onCursor cellGood) dead (updateAt A) out xs badCell inside

private theorem badTail (xs : Fin 6 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) dead out xs) :
    Nonempty (Derivation B Γ (zeroTail out)) := by
  have pack : Report (B := B) (Γ := Γ) consCode out ![z,z] := by
    apply compositionRecover consCode
      ![ID1Completion.InternalAcceptance.constantZero 6,ID1Completion.InternalAcceptance.constantZero 6]
      out xs ![z,z] held
    intro i
    exact Fin.cases (ID1Completion.InternalAcceptanceConjunctionProof.constantZeroValue xs)
      (Fin.cases (ID1Completion.InternalAcceptanceConjunctionProof.constantZeroValue xs)
        (fun k => Fin.elim0 k)) i
  exact consTail out z z pack

private theorem goodTail (g : Program 1) (raw : Program 5) (least : Program 3)
    (xs : Fin 6 → OTerm α) (out : OTerm α)
    (oldDead : Nonempty (Derivation B Γ (zeroTail (xs 1))))
    (held : Report (B := B) (Γ := Γ) (updateAt (zeroOutput g (advance raw least))) out xs) :
    Nonempty (Derivation B Γ (zeroTail out)) := by
  let A := zeroOutput g (advance raw least)
  apply programCompositionCases consCode ![onCursor cellTail,advanceAt A] out xs _ held
  intro β j parts Δ keep packed components
  rw [zeroTailRename]
  let ys := fun i => (xs i).relabel j
  have previous := renameInto oldDead j Δ keep
  rw [zeroTailRename] at previous
  have cur := currentIntro ys z previous
  have pack : Report (B := B) (Γ := Δ) consCode (out.relabel j) ![parts 0,parts 1] := by
    rw [vectorTwoEta]
    exact packed
  have tail : Report (B := B) (Γ := Δ) tailCode (parts 1) ![out.relabel j] :=
    consTail (out.relabel j) (parts 0) (parts 1) pack
  apply programCases (onCursor cellHead) ys _
  intro γ k Ω hop keep' first
  rw [zeroTailRename]
  let zs := fun i => (ys i).relabel k
  have current := renameInto cur k Ω keep'
  simp only [programRename,zRelabel] at current
  have cp := renameInto (components 1) k Ω keep'
  simp only [programRename] at cp
  have tail' := renameInto tail k Ω keep'
  simp only [programRename,vectorOneRename] at tail'
  have act := exact_OpenFilteredAdvanceDead (B := B) (Γ := Ω) g raw least (zs 2) (zs 3) hop
  have known := advanceIntro A zs z z hop current first act
  have same := valueUnique (advanceAt A) ((parts 1).relabel k) z zs cp known
  exact outputTransport tailCode ((parts 1).relabel k) z ![((out.relabel j).relabel k)] same tail'

/-- Numeric zero current is absorbing for the actual filtered STEP,
for arbitrary open old/output scratch values and literal other fields.
No constraint on the rank program, raw relation or cursor is needed. -/
theorem exact_OpenFilteredStepKeepsZero (g : Program 1) (raw : Program 5) (least : Program 3)
    (xs : Fin 6 → OTerm α) (out : OTerm α)
    (oldDead : Nonempty (Derivation B Γ (zeroTail (xs 1))))
    (held : Report (B := B) (Γ := Γ) (stepAt (zeroOutput g (advance raw least))) out xs) :
    Nonempty (Derivation B Γ (zeroTail out)) := by
  let A := zeroOutput g (advance raw least)
  apply optionGraphCases scratchCursor xs _
  · intro β j Δ keep nil
    rw [zeroTailRename]
    have h := renameInto held j Δ keep
    rw [programRename] at h
    have prev := renameInto oldDead j Δ keep
    rw [zeroTailRename] at prev
    exact compareDead A _ ((xs 1).relabel j) (out.relabel j) (nilStep A _ nil) h prev
  · intro β j Δ cur keep live
    let ys := fun i => (xs i).relabel j
    rw [zeroTailRename]
    have h := renameInto held j Δ keep
    rw [programRename] at h
    have prev := renameInto oldDead j Δ keep
    rw [zeroTailRename] at prev
    apply optionGraphCases (onCursor cellGood) ys _
    · intro γ k Ω keep' bad
      rw [zeroTailRename]
      have moved := renameInto h k Ω keep'
      rw [programRename] at moved
      have ok := renameInto live k Ω keep'
      simp only [programRename,sucRelabel] at ok
      exact badTail _ _ (badOutput A _ (cur.relabel k) _ ok bad moved)
    · intro γ k Ω mark keep' good
      rw [zeroTailRename]
      have moved := renameInto h k Ω keep'
      rw [programRename] at moved
      have lk := renameInto live k Ω keep'
      simp only [programRename,sucRelabel] at lk
      have pk := renameInto prev k Ω keep'
      rw [zeroTailRename] at pk
      exact goodTail g raw least _ _ pk (goodUpdate A _ (cur.relabel k) mark _ lk good moved)

#print axioms exact_OpenFilteredStepKeepsZero
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepDeadProof
