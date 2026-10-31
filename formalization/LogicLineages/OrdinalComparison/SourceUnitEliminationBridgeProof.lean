module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationSyntaxProof
public import LogicLineages.OrdinalComparison.SourceOneUnitProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitElimination.Proof
open OriginalDomain

theorem one_unit_graph (left right : List Ty) (σ τ : Ty) (hσ : 0<σ.level)
    (t : OriginalTerm (left++σ::right) τ) :
    ∃ d : OneUnit.Data,
      OneUnit.compile (t.rename (SelectedBinder.moveToHead left right σ))=some d ∧
      ∀ (ρ : Variable (left++σ::right) .ground → Nat) (r : Nat),
        OneUnit.Formula (UnitObservation.substitution (UnitObservation.remainingInputs left right σ ρ))
          (t.rename (SelectedBinder.moveToHead left right σ)) d r ↔ RawGraph t ρ r := by
  obtain ⟨d,hc,h,ha,hsem⟩ := OneUnit.Proof.fullSourceOneUnit.2 left right σ τ hσ t
  refine ⟨d,hc,?_⟩
  intro ρ r
  obtain ⟨R,hRpos,hRv,hform⟩ := hsem
    (UnitObservation.substitution (UnitObservation.remainingInputs left right σ ρ))
  rw [UnitObservation.Proof.selectedValuation left right σ hσ ρ] at hRv
  constructor
  · intro hf
    have hr := (hform r).mp hf
    exact ⟨h,ha,by rw [hr]; exact hRv⟩
  · rintro ⟨w,hw,he⟩
    have heq := Option.some.inj (hw.symm.trans ha)
    subst w
    apply (hform r).mpr
    exact Nat.cast_injective (he.symm.trans hRv)

theorem free_node (left right : List Ty) (σ τ : Ty)
    (a : OriginalTerm (σ::(left++right)) τ) (d : OneUnit.Data) (hf : d.free=true)
    (q : Tree (Nat×Nat) (left++right))
    (hq : ∀ (ρ : Variable (left++right) .ground → Nat) (r : Nat),
      Eval (realize q) ρ r ↔ RawGraph (OneUnit.first a) ρ r)
    (ρ : Variable (left++σ::right) .ground → Nat) (r : Nat) :
    Eval (realize (.free left right σ d.d q)) ρ r ↔
      OneUnit.Formula (UnitObservation.substitution (UnitObservation.remainingInputs left right σ ρ)) a d r := by
  change (∃ l : Nat, Eval (realize q) (UnitObservation.remainingInputs left right σ ρ) (l+1) ∧
    l+1=(d.d+1)*r+d.d) ↔ _
  simp only [OneUnit.Formula,hf,↓reduceIte]
  apply exists_congr
  intro l
  apply and_congr
  · exact hq _ (l+1)
  · rfl

theorem active_node (left right : List Ty) (σ τ : Ty)
    (a : OriginalTerm (σ::(left++right)) τ) (d : OneUnit.Data) (hf : d.free=false)
    (q s : Tree (Nat×Nat) (left++right))
    (hq : ∀ (ρ : Variable (left++right) .ground → Nat) (r : Nat),
      Eval (realize q) ρ r ↔ RawGraph (OneUnit.first a) ρ r)
    (hs : ∀ (ρ : Variable (left++right) .ground → Nat) (r : Nat),
      Eval (realize s) ρ r ↔ RawGraph (OneUnit.second a) ρ r)
    (ρ : Variable (left++σ::right) .ground → Nat) (r : Nat) :
    Eval (realize (.active left right σ (OneUnit.coefficient τ) d.d d.d' (OneUnit.constant τ d) q s)) ρ r ↔
      OneUnit.Formula (UnitObservation.substitution (UnitObservation.remainingInputs left right σ ρ)) a d r := by
  change (∃ l l' : Nat,
    Eval (realize q) (UnitObservation.remainingInputs left right σ ρ) (l+1) ∧
    Eval (realize s) (UnitObservation.remainingInputs left right σ ρ) (l'+1) ∧
    OneUnit.coefficient τ*d.d'*(l+1)+d.d*OneUnit.constant τ d=
      d.d*(l'+1)+OneUnit.coefficient τ*(d.d'-d.d)*r) ↔ _
  simp only [OneUnit.Formula,hf,Bool.false_eq_true,↓reduceIte]
  apply exists_congr
  intro l
  apply exists_congr
  intro l'
  exact and_congr (hq _ (l+1)) (and_congr (hs _ (l'+1)) Iff.rfl)
end LogicLineages.OrdinalComparison.Source.UnitElimination.Proof
