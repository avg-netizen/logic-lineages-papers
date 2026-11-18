module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGValidationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

def specCode (s : Spec) : RawSpec := (s.1.map SyntaxCode.typeCode,SyntaxCode.typeCode s.2)

theorem type_code_injective : Function.Injective SyntaxCode.typeCode := by
  intro a b h
  have := congrArg SyntaxCode.decodeType h
  simpa only [decode_type] using this
@[simp] theorem type_code_eq (a b : Ty) : SyntaxCode.typeCode a = SyntaxCode.typeCode b ↔ a=b :=
  type_code_injective.eq_iff
@[simp] theorem decode_type_eq (n : Nat) (τ : Ty) : SyntaxCode.decodeType n = τ ↔ n = SyntaxCode.typeCode τ := by
  constructor
  · intro h
    simpa only [encode_type] using congrArg SyntaxCode.typeCode h
  · intro h
    rw [h,decode_type]

theorem spec_code_injective : Function.Injective specCode := by
  rintro ⟨Δ,τ⟩ ⟨Θ,σ⟩ h
  have hl := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  have hd := congrArg (List.map SyntaxCode.decodeType) hl
  simp only [specCode,decode_types] at hd
  have he : τ=σ := type_code_injective ht
  cases hd; cases he; rfl
@[simp] theorem spec_code_eq (s t : Spec) : specCode s = specCode t ↔ s=t :=
  spec_code_injective.eq_iff

/-- Numeric acceptance is exactly success of the genuine dependent variable lookup. -/
theorem variable_status (Γ : List Ty) (τ : Ty) (i : Nat) :
    variable (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode τ) i =
      (getVariable Γ τ i).isSome := by
  induction Γ generalizing i with
  | nil => simp [variable,getVariable]
  | cons σ Γ ih =>
      cases i with
      | zero =>
          by_cases he : σ=τ <;> simp [variable,getVariable,he]
      | succ i =>
          simpa [variable,getVariable] using ih i

/-- Numeric acceptance is exactly success of the genuine dependent reference lookup. -/
theorem reference_status (ss : List Spec) (s : Spec) (i : Nat) :
    lookup (ss.map specCode) (specCode s) i = (getReference ss s i).isSome := by
  induction ss generalizing i with
  | nil => simp [lookup,getReference]
  | cons t ss ih =>
      cases i with
      | zero =>
          by_cases he : t=s <;> simp [lookup,getReference,he]
      | succ i =>
          simpa [lookup,getReference] using ih i

/-- The scan always records literal table specifications, including when validity is false. -/
theorem graph_specs (Γ : List Nat) (as : List Node) :
    (graph Γ as).1 = as.map (fun a => (a.1,a.2.1)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [graph,List.foldr_cons,scan] at *; exact ih

/-- A failed tail cannot be repaired by later local node checks. -/
theorem invalid_tail (Γ : List Nat) (a : Node) (as : List Node)
    (h : (graph Γ as).2 = false) : (graph Γ (a::as)).2 = false := by
  change ((graph Γ as).2 && nodeValid Γ a (graph Γ as).1) = false
  rw [h]
  rfl

/-- Each successful typed reconstruction has exactly the raw specification list retained by scan. -/
theorem decoded_specs (Γ : List Ty) (as : List Node) (g : Graph Γ)
    (h : decodeGraph Γ as = some g) :
    as.map (fun a => (a.1,a.2.1)) = g.1.map specCode := by
  rw [← graph_encode_of_decode Γ as g h]
  rcases g with ⟨ss,d⟩
  induction d <;> simp_all [encodeGraph,node,specCode]

@[simp] theorem variable_raw_status (Γ : List Ty) (Δ : List Nat) (t i : Nat) :
    variable (Δ ++ Γ.map SyntaxCode.typeCode) t i =
      (getVariable (Δ.map SyntaxCode.decodeType ++ Γ) (SyntaxCode.decodeType t) i).isSome := by
  have h := variable_status (Δ.map SyntaxCode.decodeType ++ Γ) (SyntaxCode.decodeType t) i
  simpa only [List.map_append,encode_types,encode_type] using h

@[simp] theorem reference_raw_status (ss : List Spec) (Δ : List Nat) (t i : Nat) :
    lookup (ss.map specCode) (Δ,t) i =
      (getReference ss (Δ.map SyntaxCode.decodeType,SyntaxCode.decodeType t) i).isSome := by
  have h := reference_status ss (Δ.map SyntaxCode.decodeType,SyntaxCode.decodeType t) i
  simpa only [specCode,encode_types,encode_type] using h

@[simp] theorem decode_arrow (a b : Nat) :
    SyntaxCode.decodeType (SyntaxCode.arrowCode a b) =
      .arrow (SyntaxCode.decodeType a) (SyntaxCode.decodeType b) := by
  have h : SyntaxCode.typeCode (.arrow (SyntaxCode.decodeType a) (SyntaxCode.decodeType b)) =
      SyntaxCode.arrowCode a b := by simp [SyntaxCode.typeCode,encode_type]
  rw [← h,decode_type]

@[simp] theorem bind_some_status {α β : Type} (x : Option α) (f : α → β) :
    (x.bind fun a => some (f a)).isSome = x.isSome := by
  cases x <;> rfl
@[simp] theorem bind_two_status {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → γ) :
    (x.bind fun a => y.bind fun b => some (f a b)).isSome = (x.isSome && y.isSome) := by
  cases x <;> cases y <;> rfl
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
