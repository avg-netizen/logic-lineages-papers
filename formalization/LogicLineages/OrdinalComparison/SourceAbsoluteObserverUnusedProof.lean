module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionEraserProof
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

def freePart {Γ m} (v : OrdinalVector Γ m) (i : Fin (m+1)) : OrdinalPartialVector Γ .ground :=
  fun j => if i.val = j.val then .add (v i) .one else .one

def unusedVector {Γ m} (v : OrdinalVector Γ m) : OrdinalVector Γ (max 1 m) :=
  fun j =>
    let delta : OrdinalExpression Γ :=
      if j.val = 0 then repeated OrdinalSyntax.defaultPolicy .scalarRepeat (2*(m+1)) (.add (v 0) .one)
      else if hj : j.val < 2 then
        AdmissibleSum.expand (OrdinalSyntax.defaultPolicy.shape .positiveAbstraction m)
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

theorem unused_assignment {Γ τ} (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (hv : assignment OrdinalSyntax.defaultPolicy t = some v) :
    assignment OrdinalSyntax.defaultPolicy (.lam (t.rename (Renaming.weaken Γ .ground))) =
      some (unusedVector v) := by
  have hp (i : Fin (τ.level+1)) :
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
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
    (Renaming.weaken Γ .ground) OrdinalSyntax.defaultPolicy t, hv]
  change abstraction OrdinalSyntax.defaultPolicy
    (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v) = some (unusedVector v)
  unfold abstraction
  rw [hsize]
  have hps : (fun i : Fin (τ.level+1) => AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val
      (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v i)) = fun i => some (freePart v i) :=
    funext hp
  rw [hps, collect_some]
  simp only [Option.bind_some]
  apply congrArg some
  funext j
  simp only [Ty.level, Nat.reduceAdd, Nat.reducePow, unusedVector, freePart,
    Fin.val_zero, ↓reduceIte, SourceRenaming.renameVector, weaken_closure]

theorem values_repeat (n a : Nat) :
    AdmissibleSum.values (List.replicate n (a : Ordinal)) = ((n*a : Nat) : Ordinal) := by
  induction n with
  | zero => simp [AdmissibleSum.values]
  | succ n ih =>
    change ordinalNaturalSum (a : Ordinal) (AdmissibleSum.values (List.replicate n (a : Ordinal))) = _
    rw [ih, naturalSum_finite]
    congr 1
    simp [Nat.succ_mul, Nat.add_comm]

theorem repeated_value {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (n a : Nat) (t : OrdinalExpression Γ) (ht : denote ν t = (a : Ordinal)) :
    denote ν (repeated OrdinalSyntax.defaultPolicy .scalarRepeat n t) = ((n*a : Nat) : Ordinal) := by
  cases n with
  | zero => simp [repeated, denote]
  | succ n =>
    simp only [repeated]
    rw [AdmissibleSum.expand_value]
    simp only [List.ofFn_const, List.map_replicate, ht]
    exact values_repeat _ _

theorem unused_scalar {Γ τ} (ν : OrdinalComponent Γ → Ordinal)
    (v : OrdinalVector Γ τ.level) (n : Nat) (hn : denote ν (v 0) = (n : Ordinal)) :
    denote ν (unusedVector v 0) = ((factor τ*n + (factor τ-1) : Nat) : Ordinal) := by
  change ordinalNaturalSum
    (denote ν (repeated OrdinalSyntax.defaultPolicy .scalarRepeat (2*(τ.level+1)) (.add (v 0) .one)))
    (denote ν (v 0)) = _
  have ht : denote ν (.add (v 0) .one) = ((n+1 : Nat) : Ordinal) := by
    change ordinalNaturalSum (denote ν (v 0)) 1 = _
    rw [hn]
    simpa only [Nat.cast_one] using naturalSum_finite n 1
  rw [repeated_value ν _ _ _ ht, hn, naturalSum_finite]
  congr 1
  unfold factor
  simp only [Nat.add_sub_cancel]
  ring
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
