module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDropProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalListCodec
open InternalListCodecSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalEqualityTestPredecessorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original nil tail is obtained from pairing inversion and predecessor
zero in the calculus, without evaluating any program. -/
theorem tailNil :
    Nonempty (Derivation body Gamma (unaryGraph tailCode (z : OTerm α) z)) := by
  have hp : Nonempty (Derivation body Gamma (pairGraph (z : OTerm α) z z)) :=
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse body α z z z) hp
  apply compositionValue InternalUnpair.right (fun _ : Fin 1 => InternalEqualityTest.predecessor)
    z (Fin.cons z Fin.elim0) (Fin.cons z Fin.elim0)
    ⟨Derivation.conjunctionRight hi⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact predecessorZero

/-- The frozen drop program is literally numeric iteration of the original
tail program. Its proved internal fixed-point induction applies at nil. -/
theorem dropNil (index : OTerm α) :
    Nonempty (Derivation body Gamma (dropGraph z index z)) :=
  InternalNumericIterationFixedPointProof.fixedValue tailCode index z tailNil

/-- Move one constructor out of the literal original drop graph. The numeric
iteration theorem is proved by induction within the original calculus. -/
theorem dropConsForward (out index code head tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hd : Nonempty (Derivation body Gamma (dropGraph out index tail))) :
    Nonempty (Derivation body Gamma (dropGraph out (suc index) code)) :=
  InternalNumericIterationProof.frontSuccBackward tailCode index out code tail
    (InternalRawListRecursionSupportProof.consTail code head tail hc) hd

/-- The converse retains the same symbolic output, constructor and index. -/
theorem dropConsBackward (out index code head tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hd : Nonempty (Derivation body Gamma (dropGraph out (suc index) code))) :
    Nonempty (Derivation body Gamma (dropGraph out index tail)) :=
  InternalNumericIterationProof.frontSuccForward tailCode index out code tail
    (InternalRawListRecursionSupportProof.consTail code head tail hc) hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDropProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDropProof
