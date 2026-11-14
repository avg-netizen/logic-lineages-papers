module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.NativeProof
open NumberedExchangeCodeFieldsProof NumberedExchangeCodePrimrecProof NumberedExchangeCode

theorem nativeRankDecrease : Targets.NativeRankDecrease := by
  intro n node param child h
  cases hn : Encodable.decode (α := Node n) node with
  | none => simp only [depsAt,hn,Option.map_none,Option.getD_none,List.not_mem_nil] at h
  | some p =>
    simp only [depsAt,hn,Option.map_some,Option.getD_some] at h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    simp only [rankAt,Encodable.decode_encode,hn,Option.map_some,Option.getD_some]
    exact dependenciesDecrease n p q hq

theorem nativeOriginalValue : Targets.NativeOriginalValue := by
  intro n arity window source target
  simp only [valueAt,Encodable.decode_encode]

theorem nativeLayerLaw : Targets.NativeLayerLaw := by
  intro n arity node param
  cases hn : Encodable.decode (α := Node n) node with
  | none => simp only [layerAt,valueAt,hn]
  | some p =>
    cases hw : Encodable.decode (α := Window n) param with
    | none => simp only [layerAt,valueAt,hn,hw]
    | some window =>
      have hvals : ((depsAt n node param).map (fun child => valueAt n arity child param)).map
          (fun value => value == 1) =
          (dependencies p).map (fun q => codeExchange arity window.1 window.2 q.1 q.2) := by
        simp only [depsAt,hn,Option.map_some,Option.getD_some,List.map_map]
        apply List.map_congr_left
        intro q hq
        simp only [Function.comp_apply,valueAt,Encodable.decode_encode,hw]
        cases codeExchange arity window.1 window.2 q.1 q.2 <;> rfl
      simp only [layerAt,valueAt,hn,hw]
      change some (layer n arity (window,fields p.1,fields p.2,
        ((depsAt n node param).map (fun child => valueAt n arity child param)).map
          (fun value => value == 1))).toNat =
        some (codeExchange arity window.1 window.2 p.1 p.2).toNat
      rw [hvals,layerCalibration]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.NativeProof
