module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
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

abbrev variableIndex : Program 3 := rightOf (.projection 2)
abbrev variableTagControl : Program 3 := sameOf (leftOf (.projection 2)) (constant 3 0)
abbrev variableBelowControl : Program 3 := .composition InternalLessThan.ltTest ![variableIndex,.projection 1]
abbrev variableEqualControl : Program 3 := sameOf variableIndex (.projection 1)
abbrev predecessorIndex : Program 3 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => variableIndex)
abbrev eraseTail : Program 3 := InternalAcceptance.branch variableEqualControl
  (pairOf (constant 3 0) predecessorIndex) (pairOf (constant 3 3) (.projection 0))
abbrev eraseDecision : Program 3 := InternalAcceptance.branch variableBelowControl eraseTail (.projection 2)

/-- The strict-above case rejects both exact arithmetic controls. -/
theorem aboveControls (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k i))) :
    Nonempty (Derivation body Delta (graph3 variableBelowControl z d k raw)) ∧
    Nonempty (Derivation body Delta (graph3 variableEqualControl z d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hi := (variableLeafSelectors raw d k i hr).2
  exact ⟨binaryValue InternalLessThan.ltTest variableIndex (.projection 1) z i k xs
      (InternalLessThanSupportProof.rejectOfGreater i k hlt) hi (projectionValue 1 xs),
    binaryValue InternalEqualityTest.equalityTest variableIndex (.projection 1) z i k xs
      (InternalEqualityTestProof.rejectBackwardOrder i k hlt) hi (projectionValue 1 xs)⟩

/-- Equality erases to bottom of the retained erased-type input, not of any
surrounding annotation. Both controls are proved in the object arithmetic. -/
theorem equalControls (raw d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (he : Nonempty (Derivation body Delta (equal i k))) :
    Nonempty (Derivation body Delta (graph3 variableBelowControl z d k raw)) ∧
    Nonempty (Derivation body Delta (graph3 variableEqualControl (numeral 1) d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hi := (variableLeafSelectors raw d k i hr).2
  have he' : Nonempty (Derivation body Delta (eqn i k)) := by simpa only [equalEqn] using he
  exact ⟨binaryValue InternalLessThan.ltTest variableIndex (.projection 1) z i k xs
      (InternalLessThanSupportProof.rejectOfEqual i k he') hi (projectionValue 1 xs),
    binaryValue InternalEqualityTest.equalityTest variableIndex (.projection 1) (numeral 1) i k xs
      (InternalEqualityTestCompositionProof.equalityOfEqual i k he') hi (projectionValue 1 xs)⟩

theorem eraseLeafBelowForward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor out i)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hdec := successorBranchElim variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 ho
  have hraw := successorBranchElim variableBelowControl eraseTail (.projection 2) out z xs
    (variableBelowValue raw d k i hr hlt) hdec
  obtain ⟨he⟩ := valueUnique (.projection (2 : Fin 3)) out raw xs hraw (projectionValue 2 xs)
  exact outputTransport variableConstructor raw out (Fin.cons i Fin.elim0) ⟨symm he⟩ hr

theorem eraseLeafBelowBackward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess i k)))
    (ho : Nonempty (Derivation body Delta (graph1 variableConstructor out i))) :
    Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have he := valueUnique variableConstructor raw out (Fin.cons i Fin.elim0) hr ho
  have hraw := outputTransport (.projection (2 : Fin 3)) raw out xs he (projectionValue 2 xs)
  have hdec := successorBranchIntro variableBelowControl eraseTail (.projection 2) out z xs
    (variableBelowValue raw d k i hr hlt) hraw
  exact successorBranchIntro variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 hdec

theorem eraseLeafEqualForward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (he : Nonempty (Derivation body Delta (equal i k)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw))) :
    Nonempty (Derivation body Delta (graph1 bottomConstructor out d)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hs := equalControls raw d k i hr he
  have hdec := successorBranchElim variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 ho
  have htail := zeroBranchElim variableBelowControl eraseTail (.projection 2) out xs hs.1 hdec
  have hp := successorBranchElim variableEqualControl (pairOf (constant 3 0) predecessorIndex)
    (pairOf (constant 3 3) (.projection 0)) out z xs hs.2 htail
  exact bottomConstructorValue out d
    (binaryRecover InternalPairing.pairing (constant 3 3) (.projection 0) out (numeral 3) d xs hp
      (constantValue 3 xs) (projectionValue 0 xs))

theorem eraseLeafEqualBackward (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (he : Nonempty (Derivation body Delta (equal i k)))
    (ho : Nonempty (Derivation body Delta (graph1 bottomConstructor out d))) :
    Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hs := equalControls raw d k i hr he
  have hp := binaryValue InternalPairing.pairing (constant 3 3) (.projection 0) out (numeral 3) d xs
    (bottomConstructorPair out d ho) (constantValue 3 xs) (projectionValue 0 xs)
  have htail := successorBranchIntro variableEqualControl (pairOf (constant 3 0) predecessorIndex)
    (pairOf (constant 3 3) (.projection 0)) out z xs hs.2 hp
  have hdec := zeroBranchIntro variableBelowControl eraseTail (.projection 2) out xs hs.1 htail
  exact successorBranchIntro variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 hdec

theorem eraseLeafAboveForwardAt (raw out d k i previous : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k i)))
    (hprevious : Nonempty (Derivation body Delta (graph1 InternalEqualityTest.predecessor previous i)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableConstructor out previous)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hs := aboveControls raw d k i hr hlt
  have hdec := successorBranchElim variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 ho
  have htail := zeroBranchElim variableBelowControl eraseTail (.projection 2) out xs hs.1 hdec
  have hp := zeroBranchElim variableEqualControl (pairOf (constant 3 0) predecessorIndex)
    (pairOf (constant 3 3) (.projection 0)) out xs hs.2 htail
  have hpred := unaryValue InternalEqualityTest.predecessor variableIndex previous i xs
    hprevious (variableLeafSelectors raw d k i hr).2
  exact variableConstructorValue out previous
    (binaryRecover InternalPairing.pairing (constant 3 0) predecessorIndex out (numeral 0) previous xs hp
      (constantValue 0 xs) hpred)

theorem eraseLeafAboveBackwardAt (raw out d k i previous : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k i)))
    (hprevious : Nonempty (Derivation body Delta (graph1 InternalEqualityTest.predecessor previous i)))
    (ho : Nonempty (Derivation body Delta (graph1 variableConstructor out previous))) :
    Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have hs := aboveControls raw d k i hr hlt
  have hpred := unaryValue InternalEqualityTest.predecessor variableIndex previous i xs
    hprevious (variableLeafSelectors raw d k i hr).2
  have hp := binaryValue InternalPairing.pairing (constant 3 0) predecessorIndex out (numeral 0) previous xs
    (variableConstructorPair out previous ho) (constantValue 0 xs) hpred
  have htail := zeroBranchIntro variableEqualControl (pairOf (constant 3 0) predecessorIndex)
    (pairOf (constant 3 3) (.projection 0)) out xs hs.2 hp
  have hdec := zeroBranchIntro variableBelowControl eraseTail (.projection 2) out xs hs.1 htail
  exact successorBranchIntro variableTagControl (.projection 2) eraseDecision out z xs
    (variableLeafSelectors raw d k i hr).1 hdec

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
