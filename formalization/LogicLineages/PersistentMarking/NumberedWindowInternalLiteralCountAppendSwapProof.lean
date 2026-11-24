module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open ID1Completion.InternalAdditionCancellationProof (commutativity)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendProof (exact_LiteralOpenCountAppend)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement agreementBody)
open NumberedWindowInternalLiteralCountConverseProof (exact_LiteralAgreementAccept)
open NumberedWindowInternalLiteralCount (entryCount permutation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swapAt (left right lr rl key lc rc : OTerm α)
    (h : Nonempty (Derivation B Γ (appended left right lr)))
    (g : Nonempty (Derivation B Γ (appended right left rl)))
    (a : Nonempty (Derivation B Γ (counted lr key lc)))
    (b : Nonempty (Derivation B Γ (counted rl key rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  apply programCases entryCount ![left,key] (eqn lc rc)
  intro β j Δ l keep leftCount
  rw [binaryInputsRename] at leftCount
  let L := left.relabel j
  let R := right.relabel j
  let LR := lr.relabel j
  let RL := rl.relabel j
  let K := key.relabel j
  let X := lc.relabel j
  let Y := rc.relabel j
  have h₁ := renamePair append lr left right h j keep
  have g₁ := renamePair append rl right left g j keep
  have a₁ := renamePair entryCount lc lr key a j keep
  have b₁ := renamePair entryCount rc rl key b j keep
  rw [eqnRelabel]
  apply programCases entryCount ![R,K] (eqn X Y)
  intro γ k Ω r retain rightCount
  rw [binaryInputsRename] at rightCount
  have h₂ := renamePair append LR L R h₁ k retain
  have g₂ := renamePair append RL R L g₁ k retain
  have a₂ := renamePair entryCount X LR K a₁ k retain
  have b₂ := renamePair entryCount Y RL K b₁ k retain
  have left₂ := renamePair entryCount l L K leftCount k retain
  obtain ⟨e⟩ := exact_LiteralOpenCountAppend (L.relabel k) (R.relabel k) (K.relabel k)
    (LR.relabel k) (l.relabel k) r (X.relabel k) h₂ left₂ rightCount a₂
  obtain ⟨f⟩ := exact_LiteralOpenCountAppend (R.relabel k) (L.relabel k) (K.relabel k)
    (RL.relabel k) r (l.relabel k) (Y.relabel k) g₂ rightCount left₂ b₂
  rw [eqnRelabel]
  exact ⟨trans e (trans (commutativity (l.relabel k) r) (symm f))⟩

theorem appendSwapAgreement (left right lr rl : OTerm α)
    (h : Nonempty (Derivation B Γ (appended left right lr)))
    (g : Nonempty (Derivation B Γ (appended right left rl))) :
    Nonempty (Derivation B Γ (agreement lr rl)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody lr rl)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let LR := lr.relabel j
  let RL := rl.relabel j
  let key : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let P := counted LR key lc ⊓ counted RL key rc
  let Δ := P :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have p : Derivation B Δ P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨eq⟩ := swapAt (left.relabel j) (right.relabel j) LR RL key lc rc
    (renamePair append lr left right h j keep) (renamePair append rl right left g j keep)
    ⟨Derivation.conjunctionLeft p⟩ ⟨Derivation.conjunctionRight p⟩
  exact ⟨Derivation.implicationIntroduction eq⟩

/-- Actual append commutation as multiplicity equivalence, not code equality. -/
theorem exact_LiteralAppendSwap (left right lr rl : OTerm α)
    (h : Nonempty (Derivation B Γ (appended left right lr)))
    (g : Nonempty (Derivation B Γ (appended right left rl))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![lr,rl])) :=
  exact_LiteralAgreementAccept B α Γ lr rl (appendSwapAgreement left right lr rl h g)

#print axioms exact_LiteralAppendSwap
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
