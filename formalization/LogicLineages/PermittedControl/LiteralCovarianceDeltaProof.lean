module
public import LogicLineages.PermittedControl.LiteralCovariancePartialProof
@[expose] public section
namespace LogicLineages.PermittedControl.LiteralCovarianceProof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment LiteralCovariance
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem collect_map {α β : Type} (k : α → β) (n : Nat) (f : Fin n → Option α) :
    collect n (fun j => (f j).map k) =
      (collect n f).map (fun v j => k (v j)) := by
  induction n with
  | zero =>
    apply congrArg some
    funext j
    exact Fin.elim0 j
  | succ n ih =>
    simp only [collect]
    rw [ih]
    cases ha : f 0 <;> cases hb : collect n (fun j => f j.succ) <;>
      simp [ha, hb]
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem subst_repeated {Γ Δ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    (site : AdmissibleSum.MacroSite) (n : Nat) (t : OrdinalExpression Γ) :
    apply r (repeated p site n t) =
      repeated p site n (apply r t) := by
  cases n with
  | zero => rfl
  | succ n => exact subst_expand r _ _

theorem delta_natural {Γ Δ σ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    {m : Nat} (h : OrdinalVector (σ :: Γ) m) :
    delta p ((fun j => apply (lift σ r) (h j))) = (delta p h).map ((fun v j => apply r (v j))) := by
  have hp : (fun i : Fin (m+1) => AdmissiblePartial.run p i.val ((fun j => apply (lift σ r) (h j)) i)) =
      (fun i : Fin (m+1) => (AdmissiblePartial.run p i.val (h i)).map (mapPartial r)) := by
    funext i
    exact partialNaturality Γ Δ σ r p i.val (h i)
  have hsize : ((List.ofFn ((fun j => apply (lift σ r) (h j)))).map ordinalPartialSize).sum =
      ((List.ofFn h).map ordinalPartialSize).sum := by
    simp only [List.map_ofFn, Function.comp_def, partial_size]
  unfold delta
  rw [hp, collect_map, hsize]
  cases hc : collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc]
  | some ps =>
    simp only [hc, Option.map_some, Option.bind_some]
    apply congrArg some
    funext j
    simp only [mapPartial]
    split_ifs <;> simp only [subst_repeated, subst_expand, head_closure, subst_add]

theorem abstraction_natural {Γ Δ σ} (r : TailSubstitution Γ Δ) (p : AdmissibleSum.Policy)
    {m : Nat} (h : OrdinalVector (σ :: Γ) m) :
    abstraction p ((fun j => apply (lift σ r) (h j))) = (abstraction p h).map ((fun v j => apply r (v j))) := by
  have hp : (fun i : Fin (m+1) => AdmissiblePartial.run p i.val ((fun j => apply (lift σ r) (h j)) i)) =
      (fun i : Fin (m+1) => (AdmissiblePartial.run p i.val (h i)).map (mapPartial r)) := by
    funext i
    exact partialNaturality Γ Δ σ r p i.val (h i)
  have hsize : ((List.ofFn ((fun j => apply (lift σ r) (h j)))).map ordinalPartialSize).sum =
      ((List.ofFn h).map ordinalPartialSize).sum := by
    simp only [List.map_ofFn, Function.comp_def, partial_size]
  unfold abstraction
  rw [hp, collect_map, hsize]
  cases hc : collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc]
  | some ps =>
    simp only [hc, Option.map_some, Option.bind_some]
    apply congrArg some
    funext j
    simp only [mapPartial]
    split_ifs <;> simp only [subst_repeated, subst_expand, head_closure, subst_add]


theorem occurrenceSizeClosure : LiteralCovarianceTargets.OccurrenceSizeClosure := by
  intro Γ Δ σ r t
  exact ⟨head_occurs r t,head_free r t,partial_size r t,head_closure r t⟩

theorem factorCovariance : LiteralCovarianceTargets.FactorCovariance := by
  intro Γ Δ σ r m h
  simp only [List.map_ofFn,Function.comp_def,partial_size]

theorem fullLiteralCovariance : LiteralCovarianceTargets.FullLiteralCovariance :=
  ⟨occurrenceSizeClosure,partialNaturality,factorCovariance,
    fun Γ Δ σ r p m h => delta_natural r p h,
    fun Γ Δ σ r p m h => abstraction_natural r p h⟩

end LogicLineages.PermittedControl.LiteralCovarianceProof
