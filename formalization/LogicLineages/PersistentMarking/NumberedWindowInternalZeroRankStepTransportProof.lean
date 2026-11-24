module

public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchIntro successorBranchIntro zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue projectionValue valueUnique outputTransport headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode tailCode)
open ID1Completion.InternalRawListRecursionSupportProof (consTail)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePositiveFold (scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6 callRename selectedRename atCursor)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankAdvanceOpenProof (exact_OpenFilteredAdvanceDead)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev Report {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α) : Prop :=
  Nonempty (Derivation B Γ (programGraph p out xs))

theorem vectorTwoEta {α : Type} (xs : Fin 2 → OTerm α) :
    ![xs 0,xs 1] = xs := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem vectorTwoRename {α β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => (![a,b] i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem vectorOneRename {α β : Type} (a : OTerm α) (j : α → β) :
    (fun i : Fin 1 => (![a] i).relabel j) = ![a.relabel j] := by
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

def zeroTail {α : Type} (s : OTerm α) : Formula α := unary tailCode z s

theorem zeroTailRename {α β : Type} (s : OTerm α) (j : α → β) :
    (zeroTail s).relabel j = zeroTail (s.relabel j) := by
  simp only [zeroTail,unaryRename,zRelabel]

theorem currentIntro (xs : Fin 6 → OTerm α) (v : OTerm α)
    (own : Report (B := B) (Γ := Γ) tailCode v ![xs 1]) :
    Report (B := B) (Γ := Γ) scratchCurrent v xs := by
  apply compositionValue tailCode (fun _ : Fin 1 => .projection 1) v xs ![xs 1] own
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 6) xs

theorem advanceIntro (A : Program 4) (xs : Fin 6 → OTerm α) (out cur hop : OTerm α)
    (hcur : Report (B := B) (Γ := Γ) scratchCurrent cur xs)
    (hhop : Report (B := B) (Γ := Γ) (onCursor cellHead) hop xs)
    (hval : Report (B := B) (Γ := Γ) A out ![xs 2,xs 3,cur,hop]) :
    Report (B := B) (Γ := Γ) (advanceAt A) out xs := by
  apply compositionValue A ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
    out xs ![xs 2,xs 3,cur,hop] hval
  intro i
  exact Fin.cases (projectionValue (2 : Fin 6) xs)
    (Fin.cases (projectionValue (3 : Fin 6) xs)
      (Fin.cases hcur (Fin.cases hhop (fun j => Fin.elim0 j)))) i

theorem updateIntro (A : Program 4) (xs : Fin 6 → OTerm α) (out tail next : OTerm α)
    (htail : Report (B := B) (Γ := Γ) (onCursor cellTail) tail xs)
    (hnext : Report (B := B) (Γ := Γ) (advanceAt A) next xs)
    (hpack : Report (B := B) (Γ := Γ) consCode out ![tail,next]) :
    Report (B := B) (Γ := Γ) (updateAt A) out xs := by
  apply compositionValue consCode ![onCursor cellTail,advanceAt A] out xs ![tail,next] hpack
  intro i
  exact Fin.cases htail (Fin.cases hnext (fun j => Fin.elim0 j)) i

theorem nilStep (A : Program 4) (xs : Fin 6 → OTerm α)
    (nilCursor : Report (B := B) (Γ := Γ) scratchCursor z xs) :
    Report (B := B) (Γ := Γ) (stepAt A) (xs 1) xs :=
  zeroBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) (xs 1) xs nilCursor
    (projectionValue (1 : Fin 6) xs)

theorem badStep (A : Program 4) (xs : Fin 6 → OTerm α) (cur out : OTerm α)
    (liveCursor : Report (B := B) (Γ := Γ) scratchCursor (suc cur) xs)
    (badCell : Report (B := B) (Γ := Γ) (onCursor cellGood) z xs)
    (hpack : Report (B := B) (Γ := Γ) consCode out ![z,z]) :
    Report (B := B) (Γ := Γ) (stepAt A) out xs := by
  have deadValue : Report (B := B) (Γ := Γ) dead out xs := by
    apply compositionValue consCode ![constantZero 6,constantZero 6] out xs ![z,z] hpack
    intro i
    exact Fin.cases (constantZeroValue xs) (Fin.cases (constantZeroValue xs) (fun j => Fin.elim0 j)) i
  have inside := zeroBranchIntro (onCursor cellGood) dead (updateAt A) out xs badCell deadValue
  exact successorBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out cur xs liveCursor inside

theorem goodStep (A : Program 4) (xs : Fin 6 → OTerm α) (cur mark out : OTerm α)
    (liveCursor : Report (B := B) (Γ := Γ) scratchCursor (suc cur) xs)
    (goodCell : Report (B := B) (Γ := Γ) (onCursor cellGood) (suc mark) xs)
    (hupdate : Report (B := B) (Γ := Γ) (updateAt A) out xs) :
    Report (B := B) (Γ := Γ) (stepAt A) out xs := by
  have inside := successorBranchIntro (onCursor cellGood) dead (updateAt A) out mark xs goodCell hupdate
  exact successorBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out cur xs liveCursor inside

private theorem unaryTailTransport (s o : OTerm α)
    (e : Nonempty (Derivation B Γ (eqn s o)))
    (hs : Nonempty (Derivation B Γ (zeroTail s))) :
    Nonempty (Derivation B Γ (zeroTail o)) :=
  headTransport tailCode z s o Fin.elim0 e hs

/-- If the step is known in the actual graph, a supplied equivalent step
output identifies its zero current. Equality transport is inside ID₁. -/
theorem compareDead (A : Program 4) (xs : Fin 6 → OTerm α) (u v : OTerm α)
    (expected : Report (B := B) (Γ := Γ) (stepAt A) u xs)
    (held : Report (B := B) (Γ := Γ) (stepAt A) v xs)
    (hzero : Nonempty (Derivation B Γ (zeroTail u))) :
    Nonempty (Derivation B Γ (zeroTail v)) :=
  unaryTailTransport u v (valueUnique (stepAt A) u v xs expected held) hzero

#print axioms nilStep
#print axioms badStep
#print axioms goodStep
#print axioms compareDead
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepTransportProof
