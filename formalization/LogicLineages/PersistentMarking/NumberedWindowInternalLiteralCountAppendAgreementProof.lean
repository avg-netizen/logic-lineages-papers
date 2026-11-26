module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementArithmeticProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalLiteralCount (permutation entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement agreementBody)
open NumberedWindowInternalLiteralCountAllQueriesChecks (exact_OpenLiteralCountAgreement)
open NumberedWindowInternalLiteralCountAgreementBindingProof (agreementRename)
open NumberedWindowInternalLiteralCountConverseProof (exact_LiteralAgreementAccept)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendAgreementArithmeticProof
  (commonPrefixCongruenceAt commonPrefixCancellationAt)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withCounts (x y w needle : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cx cy cw : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (counted (x.relabel j) (needle.relabel j) cx)) →
      Nonempty (Derivation B Δ (counted (y.relabel j) (needle.relabel j) cy)) →
      Nonempty (Derivation B Δ (counted (w.relabel j) (needle.relabel j) cw)) →
      Nonempty (Derivation B Δ (goal.relabel j))) : Nonempty (Derivation B Γ goal) := by
  apply programCases entryCount ![x,needle] goal
  intro β j Δ cx keep hx
  rw [binaryInputsRename] at hx
  let x₁ := x.relabel j
  let y₁ := y.relabel j
  let w₁ := w.relabel j
  let n₁ := needle.relabel j
  apply programCases entryCount ![y₁,n₁] (goal.relabel j)
  intro γ k Ω cy retain hy
  rw [binaryInputsRename] at hy
  let x₂ := x₁.relabel k
  let y₂ := y₁.relabel k
  let w₂ := w₁.relabel k
  let n₂ := n₁.relabel k
  have hx₂ := renamePair entryCount cx x₁ n₁ hx k retain
  apply programCases entryCount ![w₂,n₂] ((goal.relabel j).relabel k)
  intro δ m Ξ cw preserve hw
  rw [binaryInputsRename] at hw
  let ρ := m ∘ (k ∘ j)
  have hx₃ := renamePair entryCount (cx.relabel k) x₂ n₂ hx₂ m preserve
  have hy₃ := renamePair entryCount cy y₂ n₂ hy m preserve
  rw [formulaRelabelComposition j k goal,formulaRelabelComposition (k ∘ j) m goal]
  apply next δ ρ Ξ ((cx.relabel k).relabel m) (cy.relabel m) cw
    (keepThrough (k ∘ j) m (keepThrough j k keep retain) preserve)
  · simpa only [ρ,x₂,x₁,n₂,n₁,Term.relabel_relabel,counted] using hx₃
  · simpa only [ρ,y₂,y₁,n₂,n₁,Term.relabel_relabel,counted] using hy₃
  · simpa only [ρ,w₂,w₁,n₂,n₁,Term.relabel_relabel,counted] using hw

private theorem introAgreement (left right : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (key lc rc : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (counted (left.relabel j) key lc)) →
      Nonempty (Derivation B Δ (counted (right.relabel j) key rc)) →
      Nonempty (Derivation B Δ (eqn lc rc))) : Nonempty (Derivation B Γ (agreement left right)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody left right)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let key : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := counted (left.relabel j) key lc ⊓ counted (right.relabel j) key rc
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := each (α ⊕ Fin 3) j Δ key lc rc keep
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction e⟩

theorem commonPrefixCongruence (front left right jl jr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left jl)))
    (apr : Nonempty (Derivation B Γ (appended front right jr)))
    (agreed : Nonempty (Derivation B Γ (agreement left right))) :
    Nonempty (Derivation B Γ (agreement jl jr)) := by
  apply introAgreement jl jr
  intro β j Δ key u v keep cu cv
  let F := front.relabel j
  let L := left.relabel j
  let R := right.relabel j
  let JL := jl.relabel j
  let JR := jr.relabel j
  have a := renamePair append jl front left apl j keep
  have b := renamePair append jr front right apr j keep
  have g := renameInto agreed j Δ keep
  rw [agreementRename] at g
  apply withCounts F L R key (eqn u v)
  intro γ k Ω cf x y retain pf px py
  have a' := renamePair append JL F L a k retain
  have b' := renamePair append JR F R b k retain
  have g' := renameInto g k Ω retain
  rw [agreementRename] at g'
  have u' := renameInto cu k Ω retain
  have v' := renameInto cv k Ω retain
  rw [countedRename] at u' v'
  rw [eqnRelabel]
  exact commonPrefixCongruenceAt (F.relabel k) (L.relabel k) (R.relabel k) (JL.relabel k) (JR.relabel k)
    (key.relabel k) cf x y (u.relabel k) (v.relabel k) a' b' pf px py u' v' g'


theorem commonPrefixCancellation (front left right jl jr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left jl)))
    (apr : Nonempty (Derivation B Γ (appended front right jr)))
    (agreed : Nonempty (Derivation B Γ (agreement jl jr))) :
    Nonempty (Derivation B Γ (agreement left right)) := by
  apply introAgreement left right
  intro β j Δ key u v keep cu cv
  let F := front.relabel j
  let L := left.relabel j
  let R := right.relabel j
  let JL := jl.relabel j
  let JR := jr.relabel j
  have a := renamePair append jl front left apl j keep
  have b := renamePair append jr front right apr j keep
  have g := renameInto agreed j Δ keep
  rw [agreementRename] at g
  apply withCounts F JL JR key (eqn u v)
  intro γ k Ω cf x y retain pf px py
  have a' := renamePair append JL F L a k retain
  have b' := renamePair append JR F R b k retain
  have g' := renameInto g k Ω retain
  rw [agreementRename] at g'
  have u' := renameInto cu k Ω retain
  have v' := renameInto cv k Ω retain
  rw [countedRename] at u' v'
  rw [eqnRelabel]
  exact commonPrefixCancellationAt (F.relabel k) (L.relabel k) (R.relabel k) (JL.relabel k) (JR.relabel k)
    (key.relabel k) cf (u.relabel k) (v.relabel k) x y a' b' pf u' v' px py g'


theorem exact_LiteralCommonPrefixCongruence (front left right jl jr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left jl)))
    (apr : Nonempty (Derivation B Γ (appended front right jr)))
    (held : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![jl,jr])) :=
  exact_LiteralAgreementAccept B α Γ jl jr
    (commonPrefixCongruence front left right jl jr apl apr (exact_OpenLiteralCountAgreement B α Γ left right held))

theorem exact_LiteralCommonPrefixCancellation (front left right jl jr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left jl)))
    (apr : Nonempty (Derivation B Γ (appended front right jr)))
    (held : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![jl,jr]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) :=
  exact_LiteralAgreementAccept B α Γ left right
    (commonPrefixCancellation front left right jl jr apl apr (exact_OpenLiteralCountAgreement B α Γ jl jr held))

#print axioms exact_LiteralCommonPrefixCongruence
#print axioms exact_LiteralCommonPrefixCancellation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
