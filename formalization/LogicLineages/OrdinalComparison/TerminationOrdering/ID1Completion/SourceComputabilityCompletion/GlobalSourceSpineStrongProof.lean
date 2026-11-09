module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineQueriesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineStrongProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalTagArithmeticSyntaxProof (OTerm emb varBind)
open SourceComputabilityCompletion.TypedSpine GlobalSourceSpineSyntaxProof

theorem liftedDepth {α : Type} (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty) :
    lift (atDepth comp context tau (.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1))) =
      atDepth comp context tau (.var (.inr (0 : Fin 1)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)) := by
  unfold InternalStrongInduction.lift
  rw [atDepthRename]
  rfl

theorem belowDepthRename {α β : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Ty) (depth : OTerm α) (j : α → β) :
    (below (atDepth comp context tau (.var (.inr 0))) depth).relabel j =
      below (atDepth comp context tau (.var (.inr 0))) (depth.relabel j) := by
  rw [belowRename,atDepthRename]
  rfl

/-- This is the original internal course-of-values induction rule applied
to the actual depth formula. The row proof is supplied by the source edge
argument; it is not an extra assumption of the frozen I endpoint. -/
theorem fromRows {body : Positive (Fin 1)}
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (rows : ∀ (β : Type) (Delta : List (Formula β)) (depth : OTerm β),
      Nonempty (Derivation body Delta (below (atDepth comp context tau (.var (.inr 0))) depth)) →
      Nonempty (Derivation body Delta (atDepth comp context tau depth)))
    (α : Type) (Gamma : List (Formula α)) (x mark depth : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (typed comp tau (SourceComputabilityFormulaSupportProof.numeral context) x)))
    (hm : Nonempty (Derivation body Gamma (marked x mark depth))) :
    Nonempty (Derivation body Gamma (membership false x)) := by
  let theta := atDepth comp context tau (.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1))
  let Delta := below (lift theta) (.var (.inr (0 : Fin 1))) :: Gamma.map weaken
  have hb : Nonempty (Derivation body Delta (below (lift theta) (.var (.inr (0 : Fin 1))))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hrow : Nonempty (Derivation body Delta theta) := by
    have hb' := hb
    dsimp only [theta] at hb'
    rw [liftedDepth] at hb'
    exact rows (α ⊕ Fin 1) Delta (.var (.inr 0)) hb'
  obtain ⟨hall⟩ := strongInduction theta hrow
  have hd := Derivation.universalElimination (emb depth) hall
  dsimp only [theta] at hd
  rw [atDepthInstantiate] at hd
  simp only [varBind] at hd
  exact atDepthApply comp context tau depth x mark ⟨hd⟩ ht hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineStrongProof
