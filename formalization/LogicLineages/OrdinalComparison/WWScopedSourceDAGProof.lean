module
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGTargets
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDAGProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScopedDAG.Proof
open GroundEquivalence

theorem append_front {Γ ss tt} (a : DAG Γ ss) (b : DAG Γ tt) {s} (r : Ref tt s) :
    (append a b).values (Ref.front ss r)=b.values r := by
  induction b generalizing s with
  | nil => cases r
  | var d x ih => cases r with
    | here => rfl
    | there r => exact ih r
  | app d f x ih => cases r with
    | here => exact congrArg₂ Term.app (ih f) (ih x)
    | there r => exact ih r
  | lam d x ih => cases r with
    | here => exact congrArg Term.lam (ih x)
    | there r => exact ih r
  | zero d ih => cases r with
    | here => rfl
    | there r => exact ih r
  | succ d ih => cases r with
    | here => rfl
    | there r => exact ih r
  | case d τ ih => cases r with
    | here => rfl
    | there r => exact ih r
  | recursor d τ ih => cases r with
    | here => rfl
    | there r => exact ih r

theorem append_back {Γ ss tt} (a : DAG Γ ss) (b : DAG Γ tt) {s} (r : Ref ss s) :
    (append a b).values (Ref.back tt r)=a.values r := by
  induction b with
  | nil => rfl
  | var d x ih => exact ih
  | app d f x ih => exact ih
  | lam d x ih => exact ih
  | zero d ih => exact ih
  | succ d ih => exact ih
  | case d τ ih => exact ih
  | recursor d τ ih => exact ih

theorem rename_values {Γ Δ ss} (r : Source.Renaming Γ Δ) (d : DAG Γ ss) {s} (x : Ref ss s) :
    (rename r d).values x=(d.values x).rename (prefixRename r s.1) := by
  induction d generalizing s with
  | nil => cases x
  | var d y ih => cases x with
    | here => rfl
    | there x => exact ih x
  | app d f a ih => cases x with
    | here => exact congrArg₂ Term.app (ih f) (ih a)
    | there x => exact ih x
  | lam d b ih => cases x with
    | here => exact congrArg Term.lam (ih b)
    | there x => exact ih x
  | zero d ih => cases x with
    | here => rfl
    | there x => exact ih x
  | succ d ih => cases x with
    | here => rfl
    | there x => exact ih x
  | case d τ ih => cases x with
    | here => rfl
    | there x => exact ih x
  | recursor d τ ih => cases x with
    | here => rfl
    | there x => exact ih x

theorem «renaming» : Targets.Renaming := by
  intro Γ Δ τ r d
  exact ⟨rename_values r d.graph d.root,rfl⟩

theorem application : Targets.Application := by
  intro Γ σ τ f a
  constructor
  · exact congrArg₂ Term.app (append_back f.graph a.graph f.root) (append_front f.graph a.graph a.root)
  · simp only [ScopedDAG.application,List.length_cons,List.length_append]
    omega

theorem eraser : Targets.Eraser := by
  intro Γ a b
  constructor
  · exact congrArg₂ Term.app
      (congrArg Term.lam ((append_back a.graph.insert b.graph (a.root.map insertSpec)).trans
        (GroundEquivalence.Proof.insert_values a.graph a.root)))
      (append_front a.graph.insert b.graph b.root)
  · simp only [ScopedDAG.eraser,List.length_cons,List.length_append,List.length_map]
    omega

theorem detector_left_term {Γ} (a b : Input Γ .ground) :
    (detectorLeft a b).term=SourceCollisionCompletion.detectorLeft a.term b.term := by
  unfold detectorLeft SourceCollisionCompletion.detectorLeft
  rw [(eraser Γ _ _).1,(eraser Γ _ _).1,(eraser Γ _ _).1]
theorem detector_right_term {Γ} (a b : Input Γ .ground) :
    (detectorRight a b).term=SourceCollisionCompletion.detectorRight a.term b.term := by
  unfold detectorRight SourceCollisionCompletion.detectorRight
  rw [(eraser Γ _ _).1,(eraser Γ _ _).1,(eraser Γ _ _).1]
theorem detector_left_size {Γ} (a b : Input Γ .ground) :
    (detectorLeft a b).specs.length=2*(a.specs.length+b.specs.length)+6 := by
  unfold detectorLeft
  rw [(eraser Γ _ _).2,(eraser Γ _ _).2,(eraser Γ _ _).2]
  omega
theorem detector_right_size {Γ} (a b : Input Γ .ground) :
    (detectorRight a b).specs.length=2*(a.specs.length+b.specs.length)+6 := by
  unfold detectorRight
  rw [(eraser Γ _ _).2,(eraser Γ _ _).2,(eraser Γ _ _).2]
  omega

theorem aggregate : Targets.Aggregate := by
  intro Γ es
  induction es with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons e es ih =>
    rcases e with ⟨p,q⟩
    have ht1 := congrArg Prod.fst ih.1
    have ht2 := congrArg Prod.snd ih.1
    dsimp only at ht1 ht2
    constructor
    · simp only [ScopedDAG.aggregate,equations,List.map_cons,SourceAggregateCompletion.aggregate]
      rw [(eraser Γ _ _).1,(eraser Γ _ _).1,detector_left_term,detector_right_term,ht1,ht2]
      rfl
    · constructor
      · simp only [ScopedDAG.aggregate,weight,List.map_cons,List.sum_cons]
        rw [(eraser Γ _ _).2,detector_left_size,ih.2.1]
        unfold weight
        omega
      · simp only [ScopedDAG.aggregate,weight,List.map_cons,List.sum_cons]
        rw [(eraser Γ _ _).2,detector_right_size,ih.2.2]
        unfold weight
        omega
end LogicLineages.OrdinalComparison.Source.ScopedDAG.Proof
