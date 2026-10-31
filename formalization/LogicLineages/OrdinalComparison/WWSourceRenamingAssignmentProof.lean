module
public import LogicLineages.OrdinalComparison.WWSourceRenamingPartialProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRenaming.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment

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

theorem rename_repeated {Γ Δ} (r : Renaming Γ Δ) (p : AdmissibleSum.Policy)
    (site : AdmissibleSum.MacroSite) (n : Nat) (t : OrdinalExpression Γ) :
    ordinalExpressionRename r (repeated p site n t) =
      repeated p site n (ordinalExpressionRename r t) := by
  cases n with
  | zero => rfl
  | succ n => exact rename_expand r _ _

theorem rename_vectorAt {Γ Δ} (r : Renaming Γ Δ) {m : Nat}
    (v : OrdinalVector Γ m) (i : Nat) :
    ordinalExpressionRename r (ordinalVectorAt v i) = ordinalVectorAt (renameVector r v) i := by
  unfold ordinalVectorAt
  split_ifs <;> rfl

theorem rename_boxPositive {Γ Δ} (r : Renaming Γ Δ) (n : Nat)
    (f g : Nat → OrdinalExpression Γ) (i : Nat) :
    ordinalExpressionRename r (ordinalBoxPositive n f g i) =
      ordinalBoxPositive n (fun j => ordinalExpressionRename r (f j))
        (fun j => ordinalExpressionRename r (g j)) i := by
  conv_lhs => rw [ordinalBoxPositive]
  conv_rhs => rw [ordinalBoxPositive]
  by_cases hi : i ≤ n
  · simp only [hi, ↓reduceDIte, rename_emul, rename_add]
    rw [rename_boxPositive r n f g (i+1)]
  · simp [hi]
termination_by n + 1 - i
decreasing_by omega

theorem rename_boxTail {Γ Δ} (r : Renaming Γ Δ) (p : AdmissibleSum.Policy)
    (n : Nat) (a b : OrdinalExpression Γ) :
    ordinalExpressionRename r (boxTail p n a b) =
      boxTail p n (ordinalExpressionRename r a) (ordinalExpressionRename r b) := by
  unfold boxTail
  split_ifs
  · rfl
  · simp only [rename_three, numeral, rename_repeated, rename_one]

theorem application_natural {Γ Δ} (r : Renaming Γ Δ) (p : AdmissibleSum.Policy)
    {σ τ : Ty} (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level) :
    application p (renameVector r f) (renameVector r g) =
      renameVector r (application p f g) := by
  funext j
  simp only [application, box, renameVector]
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte, rename_collapse, rename_boxTail, rename_boxPositive,
      rename_vectorAt]
  · simp only [hj, ↓reduceIte, rename_boxPositive, rename_vectorAt]

theorem abstraction_natural {Γ Δ σ} (r : Renaming Γ Δ) (p : AdmissibleSum.Policy)
    {m : Nat} (h : OrdinalVector (σ :: Γ) m) :
    abstraction p (renameVector r.lift h) = (abstraction p h).map (renameVector r) := by
  have hp : (fun i : Fin (m+1) => AdmissiblePartial.run p i.val (renameVector r.lift h i)) =
      (fun i : Fin (m+1) => (AdmissiblePartial.run p i.val (h i)).map (renamePartial r)) := by
    funext i
    exact partialNaturality Γ Δ σ r p i.val (h i)
  have hsize : ((List.ofFn (renameVector r.lift h)).map ordinalPartialSize).sum =
      ((List.ofFn h).map ordinalPartialSize).sum := by
    simp only [List.map_ofFn, Function.comp_def, renameVector, partial_size]
  unfold abstraction
  rw [hp, collect_map, hsize]
  cases hc : collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc]
  | some ps =>
    simp only [hc, Option.map_some, Option.bind_some]
    apply congrArg some
    funext j
    simp only [renameVector, renamePartial]
    split_ifs <;> simp only [rename_repeated, rename_expand, head_closure, rename_add]

theorem assignmentNaturality : Targets.AssignmentNaturality := by
  intro Γ Δ τ r p t
  induction t generalizing Δ with
  | var x => rfl
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ =>
    simp only [Source.Term.rename, assignment, Option.map_some]
    apply congrArg some
    funext j
    simp only [renameVector]
    split_ifs <;> first | rfl | simp only [numeral, rename_repeated, rename_one]
  | @app Γ σ τ f a ihf iha =>
    simp only [Source.Term.rename, assignment, ihf, iha]
    cases hf : assignment p f <;> cases ha : assignment p a <;>
      simp [hf, ha, application_natural]
  | @lam Γ σ τ b ih =>
    simp only [Source.Term.rename, assignment, ih]
    cases hb : assignment p b <;> simp [hb, abstraction_natural] <;> rfl
  | ranked s _ => nomatch s
end LogicLineages.OrdinalComparison.Source.SourceRenaming.Proof
