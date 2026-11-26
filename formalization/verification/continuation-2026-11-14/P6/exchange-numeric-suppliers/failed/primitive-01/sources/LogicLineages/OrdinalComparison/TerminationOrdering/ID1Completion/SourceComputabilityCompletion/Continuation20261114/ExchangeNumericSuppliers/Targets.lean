module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Targets
def NativeRankDecrease : Prop := ∀ (n node param child : Nat),
  child ∈ depsAt n node param → rankAt n child param < rankAt n node param
/-- Pays the actual all-numeric layer law required by graph coherence.
None is never substituted for a false original answer: false is Some 0. -/
def NativeLayerLaw : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (node param : Nat),
  layerAt n arity node ((depsAt n node param).map (fun child => valueAt n arity child param)) param =
    some (valueAt n arity node param)
def NativeOriginalValue : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (window : Window n) (source target : NumberedAuxiliaryCoding.Code (Fin n)),
  valueAt n arity (Encodable.encode (source,target)) (Encodable.encode window) =
    (NumberedExchangeCode.codeExchange arity window.1 window.2 source target).toNat
/-- Genuine primitive-recursive suppliers for the explicit all-vector extension.
This does not select, install, or identify a Program with an existing opaque E. -/
def NativePrimitiveSuppliers : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (rankValue n) ∧ Primrec (depsValue n) ∧ Primrec (layerValue n arity)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers.Targets
