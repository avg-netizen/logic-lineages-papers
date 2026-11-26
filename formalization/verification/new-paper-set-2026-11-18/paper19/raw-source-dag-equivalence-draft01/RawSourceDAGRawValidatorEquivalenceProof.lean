module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorLookupProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

/-- Local numeric checking exactly reflects actual typed one-node reconstruction. -/
theorem node_status (Γ : List Ty) (a : Node) (g : Graph Γ) :
    nodeValid (Γ.map SyntaxCode.typeCode) a (g.1.map specCode) =
      (step Γ a g).isSome := by
  rcases a with ⟨Δ,t,tag,args⟩
  rcases g with ⟨ss,d⟩
  by_cases ht : tag < 7
  · interval_cases tag <;>
      rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w,args⟩⟩⟩⟩ <;>
      simp [nodeValid,step,variable_raw_status,reference_raw_status,decode_arrow,
        decode_type_eq,SyntaxCode.typeCode,SyntaxCode.caseCode,SyntaxCode.recCode,
        Ty.caseType,Ty.recType,bind_some_status,bind_two_status]
  · have hge : 7 ≤ tag := by omega
    rw [invalid_tag Γ (Δ,t,tag,args) ⟨ss,d⟩ hge]
    simp only [Option.isSome_none]
    simp [nodeValid,show tag ≠ 0 by omega,show tag ≠ 1 by omega,
      show tag ≠ 2 by omega,show tag ≠ 3 by omega,show tag ≠ 4 by omega,
      show tag ≠ 5 by omega,show tag ≠ 6 by omega]

/-- The cumulative validity bit is exactly actual graph reconstruction success.
In the failed-tail case no node is allowed to restore success. -/
theorem graph_status (Γ : List Ty) (as : List Node) :
    (graph (Γ.map SyntaxCode.typeCode) as).2 = (decodeGraph Γ as).isSome := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases hd : decodeGraph Γ as with
      | none =>
          have hn : (graph (Γ.map SyntaxCode.typeCode) as).2 = false := by simpa [hd] using ih
          rw [invalid_tail _ a as hn]
          simp [decodeGraph,hd]
      | some g =>
          have hv : (graph (Γ.map SyntaxCode.typeCode) as).2 = true := by simpa [hd] using ih
          change ((graph (Γ.map SyntaxCode.typeCode) as).2 &&
            nodeValid (Γ.map SyntaxCode.typeCode) a (graph (Γ.map SyntaxCode.typeCode) as).1) = _
          rw [hv,graph_specs,decoded_specs Γ as g hd]
          simp only [Bool.true_and,node_status,decodeGraph,hd,Option.bind_some]

theorem check_eq_valid (c : Code) : check c = valid c := by
  rcases c with ⟨Γ,as,i,t⟩
  let Δ := Γ.map SyntaxCode.decodeType
  have hc : Δ.map SyntaxCode.typeCode = Γ := encode_types Γ
  unfold check valid decode
  dsimp only
  cases hd : decodeGraph Δ as with
  | none =>
      have hn : (graph Γ as).2 = false := by
        simpa only [hc,hd,Option.isSome_none] using graph_status Δ as
      simp [Δ] at hd
      simp [hn,hd]
  | some g =>
      have hv : (graph Γ as).2 = true := by
        simpa only [hc,hd,Option.isSome_some] using graph_status Δ as
      rw [hv,graph_specs,decoded_specs Δ as g hd]
      simp only [Bool.true_and,reference_raw_status,List.map_nil]
      simp [Δ] at hd
      simp [hd,bind_some_status]
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
