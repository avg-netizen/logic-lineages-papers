module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientCalibrationProof
open Source NumberedUniformPackedDecoding JointGammaQuotient

theorem edgeCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y certificate : Nat) :
    rawEdgeTest n arity symbols S Gamma table x y certificate =
      NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate := by
  unfold rawEdgeTest NumberedNumericQuotientEdge.numericEdgeTest
  dsimp only
  rw [NumberedUniformPackedDecodingProof.rawUniverseCalibration,
    NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hq : NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma (Nat.unpair certificate).1 with
  | none => rfl
  | some q =>
    cases hr : NumberedNumericDecoding.decodePackedNumber n arity Gamma
        (Nat.unpair (Nat.unpair certificate).2).1 with
    | none => rfl
    | some r =>
      dsimp only [Option.map]
      rw [ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma q,
        ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma r]

theorem actualRawEdgeCalibration : JointGammaQuotientTargets.ActualRawEdgeCalibration := edgeCalibration

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientCalibrationProof
