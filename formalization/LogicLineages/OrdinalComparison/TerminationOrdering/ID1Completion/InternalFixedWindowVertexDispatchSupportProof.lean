module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalFixedWindowVertexDispatch InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Build the constant graph internally by its literal zero/successor AST.
Arbitrary symbolic inputs are ignored by the Program, not evaluated externally. -/
theorem constantValue (n k : Nat) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (constant n k) (numeral k) xs)) := by
  induction k with
  | zero => exact constantZeroValue xs
  | succ k ih =>
    exact unaryValue .succ (constant n k) (numeral (k+1)) (numeral k) xs
      (successorValue (Fin.cons (numeral k) Fin.elim0)) ih

theorem contextEqualityRecover (window : Nat) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same (.projection 0) (constant 5 window))
        (suc z) xs))) :
    Nonempty (Derivation body Gamma (equal (xs 0) (numeral window))) := by
  have he := binaryRecover InternalEqualityTest.equalityTest (.projection 0)
    (constant 5 window) (suc z) (xs 0) (numeral window) xs h
    (projectionValue 0 xs) (constantValue 5 window xs)
  simpa only [equalEqn] using equalityOfAcceptance (xs 0) (numeral window) he

theorem contextEqualityAccept (window : Nat) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma (equal (xs 0) (numeral window)))) :
    Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same (.projection 0) (constant 5 window))
        (suc z) xs)) := by
  apply binaryValue InternalEqualityTest.equalityTest (.projection 0)
    (constant 5 window) (suc z) (xs 0) (numeral window) xs
  · apply equalityOfEqual
    simpa only [equalEqn] using h
  · exact projectionValue 0 xs
  · exact constantValue 5 window xs

/-- The arrow graph identifies the actual output of the composed consCode.
The selected canonical typed checker remains a graph, including H and N. -/
theorem functionTypedRecover (data : Data) (xs : Fin 5 → OTerm α) (arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode arrow (xs 1) (xs 2))))
    (h : Nonempty (Derivation body Gamma (programGraph (functionTyped data) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalCertifiedSourceGuardSelection.typedAccepted data (xs 4) arrow)) := by
  have ha := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    arrow (xs 1) (xs 2) xs har (projectionValue 1 xs) (projectionValue 2 xs)
  exact binaryRecover (InternalCertifiedSourceGuardSelection.typedChecker data)
    (.projection 4) (consOf (.projection 1) (.projection 2)) (suc z) (xs 4) arrow xs
    h (projectionValue 4 xs) ha

theorem functionTypedAccept (data : Data) (xs : Fin 5 → OTerm α) (arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode arrow (xs 1) (xs 2))))
    (h : Nonempty (Derivation body Gamma
      (InternalCertifiedSourceGuardSelection.typedAccepted data (xs 4) arrow))) :
    Nonempty (Derivation body Gamma (programGraph (functionTyped data) (suc z) xs)) := by
  have ha := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    arrow (xs 1) (xs 2) xs har (projectionValue 1 xs) (projectionValue 2 xs)
  exact binaryValue (InternalCertifiedSourceGuardSelection.typedChecker data)
    (.projection 4) (consOf (.projection 1) (.projection 2)) (suc z) (xs 4) arrow xs
    h (projectionValue 4 xs) ha

theorem argumentTypedRecover (data : Data) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (argumentTyped data) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalCertifiedSourceGuardSelection.typedAccepted data (xs 3) (xs 1))) :=
  binaryRecover (InternalCertifiedSourceGuardSelection.typedChecker data)
    (.projection 3) (.projection 1) (suc z) (xs 3) (xs 1) xs h
    (projectionValue 3 xs) (projectionValue 1 xs)

theorem argumentTypedAccept (data : Data) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalCertifiedSourceGuardSelection.typedAccepted data (xs 3) (xs 1)))) :
    Nonempty (Derivation body Gamma (programGraph (argumentTyped data) (suc z) xs)) :=
  binaryValue (InternalCertifiedSourceGuardSelection.typedChecker data)
    (.projection 3) (.projection 1) (suc z) (xs 3) (xs 1) xs h
    (projectionValue 3 xs) (projectionValue 1 xs)

theorem activationRecover (window : Nat) (data : Data)
    (context domain codomain argument value arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow domain codomain)))
    (h : Nonempty (Derivation body Gamma
      (activationAccepted window data context domain codomain argument value))) :
    Nonempty (Derivation body Gamma
      (activationFactors window data context domain argument value arrow)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  have hc := conjunctionRecover _ _ xs h
  have ht := conjunctionRecover _ _ xs (andRight hc)
  exact andIntro (contextEqualityRecover window xs (andLeft hc))
    (andIntro (functionTypedRecover data xs arrow har (andLeft ht))
      (argumentTypedRecover data xs (andRight ht)))

theorem activationAccept (window : Nat) (data : Data)
    (context domain codomain argument value arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow domain codomain)))
    (h : Nonempty (Derivation body Gamma
      (activationFactors window data context domain argument value arrow))) :
    Nonempty (Derivation body Gamma
      (activationAccepted window data context domain codomain argument value)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  exact conjunctionAccept _ _ xs (contextEqualityAccept window xs (andLeft h))
    (conjunctionAccept _ _ xs
      (functionTypedAccept data xs arrow har (andLeft (andRight h)))
      (argumentTypedAccept data xs (andRight (andRight h))))

/-- Only coordinate projections are removed. The actual four-input C graph
and its arbitrary symbolic output remain unchanged. -/
theorem activeBranchRecover (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (activeBranch data) out xs))) :
    Nonempty (Derivation body Gamma (combineGraph data out (xs 1) (xs 2) (xs 4) (xs 3))) := by
  apply compositionRecover (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    ![.projection 1,.projection 2,.projection 4,.projection 3] out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4) (Fin.cons (xs 3) Fin.elim0)))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (fun j => Fin.elim0 j)))) i

theorem activeBranchAccept (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Gamma (combineGraph data out (xs 1) (xs 2) (xs 4) (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (activeBranch data) out xs)) := by
  apply compositionValue (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    ![.projection 1,.projection 2,.projection 4,.projection 3] out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4) (Fin.cons (xs 3) Fin.elim0)))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (fun j => Fin.elim0 j)))) i

theorem vertexRecover (window : Nat) (data : Data) (oldVertex : Program 5)
    (context domain codomain argument value out : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (activationAccepted window data context domain codomain argument value)))
    (h : Nonempty (Derivation body Gamma
      (vertexGraph window data oldVertex out context domain codomain argument value))) :
    Nonempty (Derivation body Gamma (combineGraph data out domain codomain value argument)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  exact activeBranchRecover data xs out
    (successorBranchElim (activation window data) oldVertex (activeBranch data) out z xs ha h)

theorem vertexAccept (window : Nat) (data : Data) (oldVertex : Program 5)
    (context domain codomain argument value out : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (activationAccepted window data context domain codomain argument value)))
    (h : Nonempty (Derivation body Gamma (combineGraph data out domain codomain value argument))) :
    Nonempty (Derivation body Gamma
      (vertexGraph window data oldVertex out context domain codomain argument value)) := by
  let xs := InternalApplicationPathMap.vertexArguments context domain codomain argument value
  exact successorBranchIntro (activation window data) oldVertex (activeBranch data) out z xs ha
    (activeBranchAccept data xs out h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
