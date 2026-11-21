module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseOrderedMinimum
open NumberedWindowInternalSparseOrderedMinimumTargets
open NumberedWindowInternalSparseOrderedMinimumOpenStepProof (pick disjRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The tail graph is the actual recursive call, not a chosen replacement
scratch pool. Its output is transported only along the step's own equation. -/
private theorem finishCell (h t k prior : OTerm α)
    (tail : Nonempty (Derivation body Γ (unary scratchMinimum prior t)))
    (offered : Nonempty (Derivation body Γ (programGraph minimumStep (suc k) ![h,prior]))) :
    Nonempty (Derivation body Γ (eqn k h ⊔ unary scratchMinimum (suc k) t)) := by
  let P := eqn k h
  let Q := eqn prior (suc k)
  let R := unary scratchMinimum (suc k) t
  obtain ⟨s⟩ := pick h prior k offered
  obtain ⟨priorGraph⟩ := tail
  have headWin : Derivation body Γ (P.imp (P ⊔ R)) :=
    Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨tailKept⟩ := outputTransport (body := body) (Gamma := Q :: Γ)
    scratchMinimum prior (suc k) ![t]
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp priorGraph Q⟩
  have tailWin : Derivation body Γ (Q.imp (P ⊔ R)) :=
    Derivation.implicationIntroduction (orRight tailKept)
  exact ⟨disjunctionElimination s headWin tailWin⟩

private theorem atCell (code h t k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (selected : Nonempty (Derivation body Γ (unary scratchMinimum (suc k) code))) :
    Nonempty (Derivation body Γ (eqn k h ⊔ unary scratchMinimum (suc k) t)) := by
  let empty : Fin 0 → OTerm α := Fin.elim0
  let result := eqn k h ⊔ unary scratchMinimum (suc k) t
  have opened := consForward (constantZero 0) minimumStep code h t (suc k) empty cell selected
  apply stepCases (constantZero 0) minimumStep (suc k) h t empty result opened
  intro β j Δ prior _ tailGraph offered
  have noInputs : (fun i => (empty i).relabel j) = (Fin.elim0 : Fin 0 → OTerm β) := by
    funext i
    exact Fin.elim0 i
  rw [noInputs] at tailGraph offered
  rw [sucRelabel] at offered
  simp only [result,disjRename,eqnRelabel,unaryRename,sucRelabel]
  exact finishCell (h.relabel j) (t.relabel j) (k.relabel j) prior tailGraph offered

theorem consOpen : ExactOpenScratchMinimumCons := by
  intro body α Γ code h t k
  let A := consGraph code h t ⊓ unary scratchMinimum (suc k) code
  have input : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨opened⟩ := atCell code h t k
    ⟨Derivation.conjunctionLeft input⟩ ⟨Derivation.conjunctionRight input⟩
  exact ⟨Derivation.implicationIntroduction opened⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenConsProof
