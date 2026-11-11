module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open Source NumberedLeastCodeRepresentative OriginalVariableDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native correspondence to the actual original dependent decoder, not a
replacement typing relation. Gamma uses its original Encodable instance,
never the separate raw packed typesNumber encoding. -/
def ActualOriginalVariableDecoderCalibration : Prop :=
  ∀ (Gamma : List Ty) (tau : Ty) (index : Nat),
    evaluate check (List.Vector.ofFn ![typeNumber tau,index,Encodable.encode Gamma]) =
      (NumberedAuxiliaryDecoding.decodeVariable Gamma tau index).isSome.toNat

/-- All outputs and arbitrary symbolic type/index; nil never succeeds,
including the exceptional ground-type code zero. -/
def ActualOriginalVariableDecoderNil : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ index : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph out typ index OrdinaryArithmetic.zeroTerm).iff
        (equal out OrdinaryArithmetic.zeroTerm)))

/-- Actual original cons graph as sole structural guard. Both accepting and
rejecting output values are retained at arbitrary raw type/head/tail codes. -/
def ActualOriginalVariableDecoderConsZero : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ code head tail : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((programGraph InternalListCodec.consCode code (Fin.cons head (Fin.cons tail Fin.elim0))).imp
        ((graph out typ OrdinaryArithmetic.zeroTerm code).iff (testSpec out typ head))))

/-- Exact original variable weakening, independently inside the arithmetic
calculus. The same output, requested type and tail context are retained.
The new head is arbitrary and need not belong to any finite type window. -/
def ActualOriginalVariableDecoderConsSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ index code head tail : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((programGraph InternalListCodec.consCode code (Fin.cons head (Fin.cons tail Fin.elim0))).imp
        ((graph out typ (OrdinaryArithmetic.succTerm index) code).iff
          (graph out typ index tail))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderTargets
