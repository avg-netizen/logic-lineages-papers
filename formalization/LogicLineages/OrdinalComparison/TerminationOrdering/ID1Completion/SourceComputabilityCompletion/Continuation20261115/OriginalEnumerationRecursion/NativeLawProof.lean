module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeInputsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeLawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric
open NativeInputsProof

def measure (node _param : Nat) : Nat := (Nat.unpair node).2
def children (node _param : Nat) : List Nat :=
  (NumberedCodeEnumerationPrimrecProof.dependencies (Nat.unpair node)).map Encodable.encode
def value (n node param : Nat) : Nat := numeric n (Nat.unpair node).2 (Nat.unpair node).1 param

theorem rankValue (node param : Nat) :
    evaluate OriginalEnumerationRecursionInterface.R (ofFn ![node,param]) = measure node param :=
  OriginalEnumerationRecursionInterface.NativeNodesProof.nativeRank (ofFn ![node,param])

theorem dependenciesValue (node param : Nat) :
    evaluate OriginalEnumerationRecursionInterface.D (ofFn ![node,param]) = numbersNumber (children node param) := by
  rw [OriginalEnumerationRecursionInterface.NativeNodesProof.nativeDependencies,
    OriginalTypeListsEnumeration.CodecProof.listEncoding]
  simp only [children,List.Vector.get_ofFn,Matrix.cons_val_zero]

theorem childDecrease (node param child : Nat) (hc : child ∈ children node param) :
    measure child param < measure node param := by
  cases hf : (Nat.unpair node).2 with
  | zero => simp only [children,NumberedCodeEnumerationPrimrecProof.dependencies,hf,List.map_nil,List.not_mem_nil] at hc
  | succ f =>
    simp only [children,NumberedCodeEnumerationPrimrecProof.dependencies,hf,List.map_cons,List.map_nil,
      Encodable.encode_prod_val,Encodable.encode_nat,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl <;> simp only [measure,Nat.unpair_pair,hf] <;> exact Nat.lt_succ_self f

theorem recursiveLaw (n node param : Nat) :
    rawCombine n node ((children node param).map (fun child => value n child param)) param = some (value n node param) := by
  cases hf : (Nat.unpair node).2 with
  | zero => simp only [rawCombine,value,hf,ite_true,numeric]
  | succ f =>
    simp only [rawCombine,value,children,NumberedCodeEnumerationPrimrecProof.dependencies,hf,
      Nat.succ_ne_zero,ite_false,numeric,List.map_cons,List.map_nil,
      Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair] <;> rfl

theorem extractValue (n node param : Nat) :
    evaluate (enumeration n) (ofFn ![node,param]) = value n node param :=
  Continuation20261114.ExchangeSelectedRecursor.NativeProof.nativeFinalValue
    OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)
    measure children (rawCombine n) (value n) rankValue dependenciesValue
    (fun node values param => NativeInputsProof.layerValue n node param values)
    childDecrease (recursiveLaw n) node param

theorem nativeNumeric : Targets.NativeNumeric := by
  intro n v
  have hvec : v.get = ![v.get 0,v.get 1] := by
    funext i
    fin_cases i <;> rfl
  have hv := congrArg List.Vector.ofFn hvec
  rw [List.Vector.ofFn_get] at hv
  conv_lhs => rw [hv]
  exact extractValue n (v.get 0) (v.get 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeLawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeLawProof
