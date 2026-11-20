module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.InternalBinderTransportProof (predicateRename)
open ID1Completion.InternalSourceIntroductionSyntaxProof (tagRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)

theorem membershipRename {α β : Type} (odd : Bool) (x : OTerm α) (j : α → β) :
    (membership odd x).relabel j = membership odd (x.relabel j) := by
  unfold membership
  rw [← predicateRename,tagRelabel]

private theorem consRename {α β : Type} (x y : OTerm α) (j : α → β) :
    (consTerm x y).relabel j = consTerm (x.relabel j) (y.relabel j) :=
  rawConsRename x y j

private theorem bottomRename {α β : Type} (c t : OTerm α) (j : α → β) :
    (packedBottomTerm c t).relabel j = packedBottomTerm (c.relabel j) (t.relabel j) := by
  simp only [packedBottomTerm,addressTerm,consRename,numeralRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel]

private theorem freeRename {α β : Type} (c t n : OTerm α) (j : α → β) :
    (packedFreeTerm c t n).relabel j =
      packedFreeTerm (c.relabel j) (t.relabel j) (n.relabel j) := by
  simp only [packedFreeTerm,consRename,numeralRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel]

variable {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveBottom (x c t : OTerm α) (j : α → β)
    (pass : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (e : Nonempty (Derivation B Γ (equal x (packedBottomTerm c t)))) :
    Nonempty (Derivation B Δ (equal (x.relabel j) (packedBottomTerm (c.relabel j) (t.relabel j)))) := by
  have h := renameInto e j Δ pass
  simp only [equalEqn,eqnRelabel,bottomRename] at h ⊢
  exact h

theorem moveFree (x c t n : OTerm α) (j : α → β)
    (pass : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (e : Nonempty (Derivation B Γ (equal x (packedFreeTerm c t n)))) :
    Nonempty (Derivation B Δ
      (equal (x.relabel j) (packedFreeTerm (c.relabel j) (t.relabel j) (n.relabel j)))) := by
  have h := renameInto e j Δ pass
  simp only [equalEqn,eqnRelabel,freeRename] at h ⊢
  exact h

theorem underSuccessor (Γ : List (Formula α)) (H : Formula (α ⊕ Fin 1)) :
    ∀ p ∈ Γ, p.relabel (Sum.inl : α → α ⊕ Fin 1) ∈ H :: Γ.map weaken :=
  fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
