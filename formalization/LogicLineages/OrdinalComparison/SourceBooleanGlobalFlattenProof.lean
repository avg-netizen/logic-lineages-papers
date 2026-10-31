module
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenTargets
public import LogicLineages.OrdinalComparison.SourceBooleanWireProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.Proof
open PrimitiveLowering BooleanFlatten

theorem all_append {α : Type} (P : α → Prop) (xs ys : List α) :
    (∀ x ∈ xs++ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),fun x hx => h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hx,hy⟩ x h
    rcases List.mem_append.mp h with h|h
    · exact hx x h
    · exact hy x h

theorem all_map {α β : Type} (P : β → Prop) (f : α → β) (xs : List α) :
    (∀ y ∈ xs.map f, P y) ↔ ∀ x ∈ xs, P (f x) := by
  constructor
  · intro h x hx
    exact h (f x) (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact h x hx

theorem all_cons {α : Type} (P : α → Prop) (x : α) (xs : List α) :
    (∀ a ∈ x::xs, P a) ↔ P x ∧ (∀ a ∈ xs, P a) := by
  simp only [List.mem_cons,forall_eq_or_imp]

theorem all_nil {α : Type} (P : α → Prop) : (∀ a ∈ ([] : List α), P a) ↔ True := by simp

theorem refPort_value {Γ n m} (a : Fin n → Port Γ) (w : Fin m → Port Γ)
    (b : Port Γ) (z : Fin 8 → Port Γ) (one : Port Γ) (ρ : OrdinalComponent Γ → Nat)
    (h : one.value ρ = 1) (r : BooleanWire.Ref n m) :
    (refPort a w b z one r).value ρ =
      r.value (fun i => (a i).value ρ) (fun i => (w i).value ρ) (b.value ρ)
        (fun i => (z i).value ρ) := by
  cases r <;> simp only [refPort,BooleanWire.Ref.value] <;> first | rfl | exact h

theorem atomGate_holds {Γ n m} (a : Fin n → Port Γ) (w : Fin m → Port Γ)
    (b : Port Γ) (z : Fin 8 → Port Γ) (one : Port Γ) (ρ : OrdinalComponent Γ → Nat)
    (h : one.value ρ = 1) (atom : BooleanWire.Atom n m) :
    (atomGate a w b z one atom).Holds ρ ↔
      atom.Holds (fun i => (a i).value ρ) (fun i => (w i).value ρ) (b.value ρ)
        (fun i => (z i).value ρ) := by
  cases atom <;> simp only [atomGate,Gate.Holds,BooleanWire.Atom.Holds,refPort_value a w b z one ρ h]

theorem flattenExact : Targets.FlattenExact := by
  intro Γ n m d a w z one ρ ho
  induction d with
  | nil => simp [flatten,BooleanWire.Holds]
  | @snoc m d g ih =>
      simp only [flatten,all_append,all_map,atomGate_holds a _ _ _ one ρ ho]
      exact and_congr (ih _ _) Iff.rfl

@[simp] theorem inputPort_value {Γ} (m : Nat) (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat) (a : Port Γ) :
    (inputPort m a).value (extend ρ (9*m+1) v) = a.value ρ := by
  cases a with
  | zero => rfl
  | var x => exact PrimitiveLowering.Proof.extend_shift ρ (9*m+1) v x 0

@[simp] theorem bitPort_value {Γ m} (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat) (i : Fin m) :
    (bitPort (Γ:=Γ) i).value (extend ρ (9*m+1) v) = v (bitIndex i) :=
  PrimitiveLowering.Proof.extend_fresh ρ (9*m+1) v (bitIndex i)

@[simp] theorem auxPort_value {Γ m} (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat) (i : Fin m) (j : Fin 8) :
    (auxPort (Γ:=Γ) i j).value (extend ρ (9*m+1) v) = v (auxIndex i j) :=
  PrimitiveLowering.Proof.extend_fresh ρ (9*m+1) v (auxIndex i j)

@[simp] theorem onePort_value {Γ} (m : Nat) (ρ : OrdinalComponent Γ → Nat)
    (v : Fin (9*m+1) → Nat) :
    (onePort (Γ:=Γ) m).value (extend ρ (9*m+1) v) = v (oneIndex m) :=
  PrimitiveLowering.Proof.extend_fresh ρ (9*m+1) v (oneIndex m)

theorem sharedInputs : Targets.SharedInputs := by
  intro Γ m ρ v
  exact ⟨fun τ x j => PrimitiveLowering.Proof.extend_shift ρ (9*m+1) v x j,
    bitPort_value ρ v,auxPort_value ρ v,onePort_value m ρ v⟩

theorem globalExact : Targets.GlobalExact := by
  intro Γ n m d a root ρ v
  unfold Holds compile
  simp only [all_cons,all_append,all_nil,and_true,Gate.Holds,onePort_value,bitPort_value]
  constructor
  · rintro ⟨ho,hf,hr⟩
    refine ⟨ho,?_,by omega⟩
    have hh := (flattenExact (Global Γ m) n m d (fun i => inputPort m (a i))
      bitPort auxPort (onePort m) (extend ρ (9*m+1) v) (by simpa using ho)).mp hf
    simpa only [inputPort_value,bitPort_value,auxPort_value] using hh
  · rintro ⟨ho,hf,hr⟩
    refine ⟨ho,?_,by omega⟩
    apply (flattenExact (Global Γ m) n m d (fun i => inputPort m (a i))
      bitPort auxPort (onePort m) (extend ρ (9*m+1) v) (by simpa using ho)).mpr
    simpa only [inputPort_value,bitPort_value,auxPort_value] using hf

@[simp] theorem pack_bit {m} (w : Fin m → Nat) (z : Fin m → Fin 8 → Nat) (i : Fin m) :
    pack w z (bitIndex i) = w i := by
  have hi : (bitIndex i).val < 9*m := by simp only [bitIndex]; omega
  have hz : (bitIndex i).val % 9 = 0 := by simp only [bitIndex]; omega
  simp only [pack,dif_pos hi,dif_pos hz]
  congr 1
  apply Fin.ext
  simp only [bitIndex]
  omega

@[simp] theorem pack_aux {m} (w : Fin m → Nat) (z : Fin m → Fin 8 → Nat)
    (i : Fin m) (j : Fin 8) : pack w z (auxIndex i j) = z i j := by
  have hi : (auxIndex i j).val < 9*m := by simp only [auxIndex]; omega
  have hz : (auxIndex i j).val % 9 ≠ 0 := by simp only [auxIndex]; omega
  simp only [pack,dif_pos hi,dif_neg hz]
  congr 1 <;> apply Fin.ext <;> simp only [auxIndex] <;> omega

@[simp] theorem pack_one {m} (w : Fin m → Nat) (z : Fin m → Fin 8 → Nat) :
    pack w z (oneIndex m) = 1 := by
  have hi : ¬ (oneIndex m).val < 9*m := by simp [oneIndex]
  simp only [pack,dif_neg hi]

theorem existentialExact : Targets.ExistentialExact := by
  intro Γ n m d a root ρ
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨_,hh,hr⟩ := (globalExact Γ n m d a root ρ v).mp hv
    exact (BooleanWire.Proof.rootCorrect n m d (fun i => (a i).value ρ) root).mp ⟨_,_,hh,hr⟩
  · intro ht
    obtain ⟨w,z,hh,hr⟩ := (BooleanWire.Proof.rootCorrect n m d (fun i => (a i).value ρ) root).mpr ht
    refine ⟨pack w z,(globalExact Γ n m d a root ρ _).mpr ?_⟩
    simpa only [pack_one,pack_bit,pack_aux,true_and] using And.intro hh hr

theorem flatten_length {Γ n m} (d : BooleanWire.Dag n m) (a : Fin n → Port Γ)
    (w : Fin m → Port Γ) (z : Fin m → Fin 8 → Port Γ) (one : Port Γ) :
    (flatten d a w z one).length = BooleanWire.atomCount d := by
  induction d with
  | nil => rfl
  | @snoc m d g ih => simp only [flatten,List.length_append,List.length_map,BooleanWire.atomCount,ih]

theorem linearOverhead : Targets.LinearOverhead := by
  intro Γ n m d a root
  have hl : (compile d a root).length = BooleanWire.atomCount d+2 := by
    simp only [compile,List.length_cons,List.length_append,List.length_singleton,List.length_nil,flatten_length]
  refine ⟨hl,?_,?_⟩
  · have hb := (BooleanWire.Proof.linearOverhead.2 n m d).1
    omega
  · simp [Global]
end LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.Proof
