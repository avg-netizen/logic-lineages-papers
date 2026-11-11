module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionTargets
open Source NumberedLeastCodeRepresentative OriginalContextExtension
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact calibration of the EXISTING Ty, List Ty and Object Encodable
instances. In particular Gamma uses Encodable.encode, not typesNumber.
These native equalities do not supply object-calculus derivations. -/
def ActualOriginalContextEncodingCalibration : Prop :=
  (∀ sigma : Ty, Encodable.encode sigma = typeNumber sigma) ∧
  (∀ (sigma : Ty) (Gamma : List Ty),
    Encodable.encode (sigma :: Gamma) =
      Nat.succ (Nat.pair (typeNumber sigma) (Encodable.encode Gamma))) ∧
  (∀ (Gamma : List Ty) (raw : Nat),
    ContextUniform.objectCode Gamma raw = Nat.pair (Encodable.encode Gamma) raw)

/-- The already fixed original cons AST agrees with the actual Encodable
context extension at its original type-number input. Separate from the
symbolic runtime bridge and not a premise of that internal derivation. -/
def ActualOriginalContextConsCalibration : Prop :=
  ∀ (sigma : Ty) (Gamma : List Ty),
  evaluate InternalListCodec.consCode
    (List.Vector.ofFn ![typeNumber sigma,Encodable.encode Gamma]) =
      Encodable.encode (sigma :: Gamma)

/-- Arbitrary symbolic d is retained. The original source Object and its raw
payload are unchanged while one original cons extension supplies the body
Object and the runtime parameters at a shared outer context. This supports
the context bookkeeping of paper06 lem:id1's lambda paragraph only; lambda
construction, body typing, source-step laws and computability remain unpaid. -/
def ActualOriginalContextExtensionRuntime : Prop := RuntimeExtension

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionTargets
