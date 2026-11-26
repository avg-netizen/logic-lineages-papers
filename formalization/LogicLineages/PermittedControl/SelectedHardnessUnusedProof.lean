module
public import LogicLineages.PermittedControl.SelectedHardnessCoordinatesProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessUnusedProof
open OrdinalComparison Source Source.AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

theorem shape1 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 1 = .join .leaf .leaf :=
  ControlSensitivityCurrent.PolicyGadget.smallShapes.2.2 _

def freePart {Γ m} (v : OrdinalVector Γ m) (i : Fin (m+1)) : OrdinalPartialVector Γ .ground :=
  fun j => if i.val = j.val then .add (v i) .one else .one

def unusedVector (p : AdmissibleSum.Policy) {Γ m} (v : OrdinalVector Γ m) : OrdinalVector Γ (max 1 m) :=
  fun j =>
    let delta : OrdinalExpression Γ :=
      if j.val = 0 then repeated p .scalarRepeat (2*(m+1)) (.add (v 0) .one)
      else if hj : j.val < 2 then
        AdmissibleSum.expand (p.shape .positiveAbstraction m)
          (fun i => freePart v i ⟨j.val, hj⟩)
      else v ⟨j.val, by have := j.isLt; omega⟩
    if hm : j.val < m+1 then .add delta (v ⟨j.val, hm⟩) else delta

theorem collect_some {α : Type} (n : Nat) (f : Fin n → α) :
    collect n (fun i => some (f i)) = some f := by
  induction n with
  | zero => apply congrArg some; funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [collect, ih, Option.bind_some]
    apply congrArg some
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem unused_assignment (p : AdmissibleSum.Policy) {Γ τ} (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (hv : assignment p t = some v) :
    assignment p (.lam (t.rename (Renaming.weaken Γ .ground))) =
      some (unusedVector p v) := by
  have hp (i : Fin (τ.level+1)) :
      AdmissiblePartial.run p i.val
        (ordinalExpressionRename (Renaming.weaken Γ .ground) (v i)) = some (freePart v i) := by
    rw [AdmissiblePartial.run.eq_def, weaken_free]
    simp only [↓reduceIte]
    apply congrArg some
    funext j
    simp only [ordinalFreePartialVector, weaken_closure, freePart]
  have hz (i : Fin (τ.level+1)) :
      ordinalPartialSize (ordinalExpressionRename (Renaming.weaken Γ .ground) (v i)) = 1 := by
    rw [ordinalPartialSize.eq_def, weaken_free]
    rfl
  have hsize : ((List.ofFn (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v)).map
      ordinalPartialSize).sum = τ.level+1 := by
    simp [List.map_ofFn, Function.comp_def, SourceRenaming.renameVector, hz, Nat.add_comm]
  simp only [assignment]
  rw [SourceRenaming.Proof.assignmentNaturality Γ (.ground::Γ) τ
    (Renaming.weaken Γ .ground) p t, hv]
  change abstraction p
    (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v) = some (unusedVector p v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin (τ.level+1) => AdmissiblePartial.run p i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v i)) = fun i => some (freePart v i) :=
    funext hp
  rw [hps, collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  simp only [Ty.level, Nat.reduceAdd, Nat.reducePow, unusedVector, freePart,
    Fin.val_zero, ↓reduceIte, SourceRenaming.renameVector, weaken_closure]


end LogicLineages.PermittedControl.SelectedHardnessUnusedProof
