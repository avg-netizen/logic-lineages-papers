module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsShiftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (consForward)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendSwapProof (exact_LiteralAppendSwap)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalLiteralCountConsAgreementProof (exact_LiteralConsCongruence)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private structure ShiftReports (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (head left right hl hr first last : OTerm α) : Prop where
  consL : Nonempty (Derivation B Γ (consGraph hl head left))
  consR : Nonempty (Derivation B Γ (consGraph hr head right))
  appendL : Nonempty (Derivation B Γ (appended hl right first))
  appendR : Nonempty (Derivation B Γ (appended left hr last))

private theorem renameReports {β : Type} {Δ : List (Formula β)}
    (head left right hl hr first last : OTerm α)
    (h : ShiftReports B Γ head left right hl hr first last) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    ShiftReports B Δ (head.relabel j) (left.relabel j) (right.relabel j) (hl.relabel j)
      (hr.relabel j) (first.relabel j) (last.relabel j) := by
  have l := renameInto h.consL j Δ keep
  have r := renameInto h.consR j Δ keep
  rw [consGraphRename] at l r
  exact ⟨l,r,renamePair append first hl right h.appendL j keep,
    renamePair append last left hr h.appendR j keep⟩

private theorem tapeTwo (x y : OTerm α) :
    (![x,y] : Fin 2 → OTerm α) = Fin.cons x (Fin.cons y Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem headAtAppend (whole head tail suffix joined out : OTerm α)
    (c : Nonempty (Derivation B Γ (consGraph whole head tail)))
    (a : Nonempty (Derivation B Γ (appended tail suffix joined)))
    (o : Nonempty (Derivation B Γ (appended whole suffix out))) :
    Nonempty (Derivation B Γ (consGraph out head joined)) := by
  simp only [appended,tapeTwo] at a o
  exact consForward whole head tail suffix joined out c a o

private theorem withSwapped (head left right hl hr first last lr rl : OTerm α)
    (h : ShiftReports B Γ head left right hl hr first last)
    (a : Nonempty (Derivation B Γ (appended left right lr)))
    (b : Nonempty (Derivation B Γ (appended right left rl))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![first,last])) := by
  apply programCases append ![hr,left] _
  intro β j Δ swapped keep hd
  rw [binaryInputsRename] at hd
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  let H := head.relabel j
  let L := left.relabel j
  let R := right.relabel j
  let HL := hl.relabel j
  let HR := hr.relabel j
  let X := first.relabel j
  let Y := last.relabel j
  let LR := lr.relabel j
  let RL := rl.relabel j
  have h' := renameReports head left right hl hr first last h j keep
  have a' := renamePair append lr left right a j keep
  have b' := renamePair append rl right left b j keep
  have firstCons := headAtAppend HL H L R LR X h'.consL a' h'.appendL
  have secondCons := headAtAppend HR H R L RL swapped h'.consR b' hd
  have p := exact_LiteralConsCongruence H LR RL X swapped firstCons secondCons
    (exact_LiteralAppendSwap L R LR RL a' b')
  exact exact_LiteralObserverTransitivity X swapped Y p
    (exact_LiteralAppendSwap HR L swapped Y hd h'.appendR)

/-- Move one actual chosen head from one append operand to the other.
The original left and right cons graphs and exact ordered append reports
are all kept, and no multiplication of equal heads is inferred. -/
theorem exact_LiteralConsShift (head left right hl hr first last : OTerm α)
    (consL : Nonempty (Derivation B Γ (consGraph hl head left)))
    (consR : Nonempty (Derivation B Γ (consGraph hr head right)))
    (appendL : Nonempty (Derivation B Γ (appended hl right first)))
    (appendR : Nonempty (Derivation B Γ (appended left hr last))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![first,last])) := by
  let h : ShiftReports B Γ head left right hl hr first last := ⟨consL,consR,appendL,appendR⟩
  apply programCases append ![left,right] _
  intro β j Δ lr keep a
  rw [binaryInputsRename] at a
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  let H := head.relabel j
  let L := left.relabel j
  let R := right.relabel j
  let HL := hl.relabel j
  let HR := hr.relabel j
  let X := first.relabel j
  let Y := last.relabel j
  have h' := renameReports head left right hl hr first last h j keep
  apply programCases append ![R,L] (programGraph permutation (suc z) ![X,Y])
  intro γ k Ω rl retain b
  rw [binaryInputsRename] at b
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  exact withSwapped (H.relabel k) (L.relabel k) (R.relabel k) (HL.relabel k) (HR.relabel k)
    (X.relabel k) (Y.relabel k) (lr.relabel k) rl
    (renameReports H L R HL HR X Y h' k retain) (renamePair append lr L R a k retain) b

#print axioms exact_LiteralConsShift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsShiftProof
