module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Continuation20261114
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem exchangeValue (n : Nat) (arity : Fin n → Nat) (seed param : Nat) :
    evaluate (OriginalDecodedExchangeEquation.exchange n arity) (ofFn ![seed,param]) =
      ExchangeNumericSuppliers.valueAt n arity seed param := by
  have hr : ∀ seed param, evaluate (OriginalDecodedRank.rank n) (ofFn ![seed,param]) = ExchangeNumericSuppliers.rankAt n seed param := by
    intro seed param
    exact OriginalDecodedRank.NativeProof.nativeOriginalRank n _
  have hd : ∀ node param, evaluate (OriginalDecodedDependencies.dependencies n) (ofFn ![node,param]) = numbersNumber (ExchangeNumericSuppliers.depsAt n node param) := by
    intro node param
    exact OriginalDecodedDependencies.NativeProof.nativeOriginalSupplier n _
  have hg : ∀ node vals param, evaluate (OriginalDecodedLayerCalibration.layer n arity) (ofFn ![node,numbersNumber vals,param]) =
      Encodable.encode (ExchangeNumericSuppliers.layerAt n arity node vals param) := by
    intro node vals param
    rw [OriginalDecodedLayerCalibration.NativeProof.nativeLayer]
    simp only [ExchangeNumericSuppliers.layerValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,numbersRoundTrip,Option.getD_some]
  exact ExchangeSelectedRecursor.NativeProof.nativeFinalValue
    (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
    _ _ _ _ hr hd hg (ExchangeNumericSuppliers.NativeProof.nativeRankDecrease n)
    (ExchangeNumericSuppliers.NativeProof.nativeLayerLaw n arity) seed param

theorem exchangeAllVectors (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    evaluate (OriginalDecodedExchangeEquation.exchange n arity) v =
      ExchangeNumericSuppliers.valueAt n arity (v.get 0) (v.get 1) := by
  have hvec : v.get = ![v.get 0,v.get 1] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have hv := congrArg List.Vector.ofFn hvec
  rw [List.Vector.ofFn_get] at hv
  rw [hv]
  exact exchangeValue n arity _ _

theorem nativeStructural : Targets.NativeStructural := by
  intro n arity v
  exact InstalledExchangeRecursor.NativeProof.nativeStructural n arity
    (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
    (OriginalStructuralDecoderSuppliers.valid n) (OriginalStructuralDecoderSuppliers.window n)
    (exchangeAllVectors n arity) (OriginalStructuralDecoderSuppliers.NativeProof.nativeValid n)
    (OriginalStructuralDecoderSuppliers.NativeProof.nativeWindow n) v
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.NativeProof
