module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRoundtripProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence

theorem variable_index_sound (Γ : List Ty) (τ : Ty) (i : Nat) (x : Variable Γ τ)
    (h : getVariable Γ τ i = some x) : variableIndex x = i := by
  induction Γ generalizing i with
  | nil => simp [getVariable] at h
  | cons σ Γ ih =>
      cases i with
      | zero =>
          simp only [getVariable] at h
          split at h
          next he => cases he; cases Option.some.inj h; rfl
          next he => simp at h
      | succ i =>
          simp only [getVariable,Option.map_eq_some_iff] at h
          obtain ⟨y,hy,hx⟩ := h
          subst x
          simp [variableIndex,ih i y hy]

theorem reference_index_sound (ss : List Spec) (s : Spec) (i : Nat) (r : Ref ss s)
    (h : getReference ss s i = some r) : referenceIndex r = i := by
  induction ss generalizing i with
  | nil => simp [getReference] at h
  | cons t ss ih =>
      cases i with
      | zero =>
          simp only [getReference] at h
          split at h
          next he => cases he; cases Option.some.inj h; rfl
          next he => simp at h
      | succ i =>
          simp only [getReference,Option.map_eq_some_iff] at h
          obtain ⟨r',hr,he⟩ := h
          subst r
          simp [referenceIndex,ih i r' hr]

/-- Successful one-node reconstruction preserves the literal node and the previous table. -/
theorem step_encode (Γ : List Ty) (a : Node) (g g' : Graph Γ)
    (h : step Γ a g = some g') :
    encodeGraph g'.2 = a :: encodeGraph g.2 := by
  rcases a with ⟨Δ,t,tag,args⟩
  rcases g with ⟨ss,d⟩
  unfold step at h
  dsimp only at h
  split at h
  · obtain ⟨x,hx,he⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj he
    simp [encodeGraph,node,encode_types,encode_type,variable_index_sound _ _ _ _ hx]
  · obtain ⟨r,hr,he⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x,hx,he⟩ := Option.bind_eq_some_iff.mp he
    cases Option.some.inj he
    simp [encodeGraph,node,encode_types,encode_type,
      reference_index_sound _ _ _ _ hr,reference_index_sound _ _ _ _ hx]
  · split at h
    next ht =>
      obtain ⟨r,hr,he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      have ht' := congrArg SyntaxCode.typeCode ht
      simp only [encode_type] at ht'
      simp [encodeGraph,node,encode_types,encode_type,
        reference_index_sound _ _ _ _ hr,← ht']
    next ht => simp at h
  · split at h
    next ht =>
      cases Option.some.inj h
      have ht' := congrArg SyntaxCode.typeCode ht
      simp only [encode_type] at ht'
      simp [encodeGraph,node,encode_types,← ht']
    next ht => simp at h
  · split at h
    next ht =>
      cases Option.some.inj h
      have ht' := congrArg SyntaxCode.typeCode ht
      simp only [encode_type] at ht'
      simp [encodeGraph,node,encode_types,← ht']
    next ht => simp at h
  · split at h
    next ht =>
      cases Option.some.inj h
      have ht' := congrArg SyntaxCode.typeCode ht
      simp only [encode_type] at ht'
      simp [encodeGraph,node,encode_types,encode_type,← ht']
    next ht => simp at h
  · split at h
    next ht =>
      cases Option.some.inj h
      have ht' := congrArg SyntaxCode.typeCode ht
      simp only [encode_type] at ht'
      simp [encodeGraph,node,encode_types,encode_type,← ht']
    next ht => simp at h
  · simp at h

theorem graph_encode_of_decode (Γ : List Ty) (as : List Node) (g : Graph Γ)
    (h : decodeGraph Γ as = some g) : encodeGraph g.2 = as := by
  induction as generalizing g with
  | nil => cases Option.some.inj h; rfl
  | cons a as ih =>
      obtain ⟨d,hd,hs⟩ := Option.bind_eq_some_iff.mp h
      rw [step_encode Γ a d g hs,ih d hd]

theorem encode_of_decode (c : Code) (d : Packed) (h : decode c = some d) :
    encode d = c := by
  rcases c with ⟨Γ,as,i,t⟩
  unfold decode at h
  obtain ⟨g,hg,he⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r,hr,he⟩ := Option.bind_eq_some_iff.mp he
  cases Option.some.inj he
  simp [encode,encode_types,encode_type,graph_encode_of_decode _ _ _ hg,
    reference_index_sound _ _ _ _ hr]

theorem valid_iff (c : Code) : valid c = true ↔ ∃ d : Packed, encode d = c := by
  unfold valid
  cases h : decode c with
  | none =>
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_exists]
      intro d he
      have hd := input_roundtrip d
      rw [he,h] at hd
      contradiction
  | some d =>
      simp only [Option.isSome_some,true_iff]
      exact ⟨d,encode_of_decode c d h⟩

theorem reify_exact (c : Code) : reifyCode c = if valid c then some c else none := by
  unfold reifyCode valid
  cases h : decode c with
  | none => rfl
  | some d => simp [encode_of_decode c d h]

theorem invalid_tag (Γ : List Ty) (a : Node) (g : Graph Γ)
    (h : 7 ≤ a.2.2.1) : step Γ a g = none := by
  rcases a with ⟨Δ,t,tag,args⟩
  rcases g with ⟨ss,d⟩
  unfold step
  dsimp only
  split <;> simp_all <;> omega

theorem validation : RawSourceDAGTargets.Validation :=
  ⟨encode_of_decode,valid_iff,typedAccepted,reify_exact,invalid_tag⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG
