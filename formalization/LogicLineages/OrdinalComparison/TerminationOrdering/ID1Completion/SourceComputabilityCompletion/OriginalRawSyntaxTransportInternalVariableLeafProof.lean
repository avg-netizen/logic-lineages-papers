module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rank counts the literal variable occurrence, irrespective of its index. -/
theorem rankLeafForward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .rank) out d k raw))) :
    Nonempty (Derivation body Delta (equal out (numeral 1))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hc := successorBranchElim (sameOf (leftOf (.projection 2)) (constant 3 0))
    (constant 3 0) (constant 3 1) out z xs (variableLeafSelectors raw d k i hr).1 ho
  simpa only [equalEqn] using valueUnique (constant 3 1) out (numeral 1) xs hc (constantValue 1 xs)

theorem rankLeafBackward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (he : Nonempty (Derivation body Delta (equal out (numeral 1)))) :
    Nonempty (Derivation body Delta (graph3 (leaf .rank) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have he' : Nonempty (Derivation body Delta (eqn out (numeral 1))) := by
    simpa only [equalEqn] using he
  obtain ⟨he'⟩ := he'
  exact successorBranchIntro (sameOf (leftOf (.projection 2)) (constant 3 0))
    (constant 3 0) (constant 3 1) out z xs (variableLeafSelectors raw d k i hr).1
    (outputTransport (constant 3 1) (numeral 1) out xs ⟨symm he'⟩ (constantValue 1 xs))

/-- A symbolic chosen index suffices to recover the literal variable result;
this helper unfolds only the fixed leaf AST, never the traversal. -/
theorem shiftLeafForwardAt (raw out d k i next : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hn : Nonempty (Derivation body Delta (graph3
      (InternalAcceptance.branch
        (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
        (succOf (rightOf (.projection 2))) (rightOf (.projection 2))) next d k raw)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .shift) out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor out next)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  let choice : Program 3 := InternalAcceptance.branch
    (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
    (succOf (rightOf (.projection 2))) (rightOf (.projection 2))
  have hc := successorBranchElim (sameOf (leftOf (.projection 2)) (constant 3 0))
    (.projection 2) (pairOf (constant 3 0) choice) out z xs
    (variableLeafSelectors raw d k i hr).1 ho
  exact variableConstructorValue out next
    (binaryRecover InternalPairing.pairing (constant 3 0) choice out (numeral 0) next xs
      hc (constantValue 0 xs) hn)

theorem shiftLeafBackwardAt (raw out d k i next : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hn : Nonempty (Derivation body Delta (graph3
      (InternalAcceptance.branch
        (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
        (succOf (rightOf (.projection 2))) (rightOf (.projection 2))) next d k raw)))
    (ho : Nonempty (Derivation body Delta (graph1 variableConstructor out next))) :
    Nonempty (Derivation body Delta (graph3 (leaf .shift) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  let choice : Program 3 := InternalAcceptance.branch
    (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
    (succOf (rightOf (.projection 2))) (rightOf (.projection 2))
  have hc := binaryValue InternalPairing.pairing (constant 3 0) choice out (numeral 0) next xs
    (variableConstructorPair out next ho) (constantValue 0 xs) hn
  exact successorBranchIntro (sameOf (leftOf (.projection 2)) (constant 3 0))
    (.projection 2) (pairOf (constant 3 0) choice) out z xs
    (variableLeafSelectors raw d k i hr).1 hc

theorem shiftChoiceBelow (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k))) :
    Nonempty (Derivation body Delta (graph3
      (InternalAcceptance.branch
        (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
        (succOf (rightOf (.projection 2))) (rightOf (.projection 2))) i d k raw)) :=
  successorBranchIntro
    (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
    (succOf (rightOf (.projection 2))) (rightOf (.projection 2)) i z
    (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0)))
    (variableBelowValue raw d k i hr hlt) (variableLeafSelectors raw d k i hr).2

theorem shiftChoiceNotBelow (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k).not)) :
    Nonempty (Derivation body Delta (graph3
      (InternalAcceptance.branch
        (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
        (succOf (rightOf (.projection 2))) (rightOf (.projection 2))) (suc i) d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hs := unaryValue .succ (rightOf (.projection 2)) (suc i) i xs
    (successorValue (Fin.cons i Fin.elim0)) (variableLeafSelectors raw d k i hr).2
  exact zeroBranchIntro
    (.composition InternalLessThan.ltTest ![rightOf (.projection 2),.projection 1])
    (succOf (rightOf (.projection 2))) (rightOf (.projection 2)) (suc i) xs
    (variableNotBelowValue raw d k i hr hlt) hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableLeafProof
