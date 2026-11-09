module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open UniformCertificateCompletion.Path
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof GuardedSourceSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem equalReverse (s t : OTerm α)
    (h : Nonempty (Derivation body Delta (equal s t))) :
    Nonempty (Derivation body Delta (equal t s)) := by
  simp only [equalEqn] at h ⊢
  obtain ⟨h⟩ := h
  exact ⟨symm h⟩

theorem equalReflexive (s : OTerm α) :
    Nonempty (Derivation body Delta (equal s s)) := by
  rw [equalEqn]
  exact ⟨refl s⟩

theorem constantValue (n k : Nat) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Delta (programGraph (Path.constant n k) (numeral k) xs)) := by
  induction k with
  | zero => exact constantZeroValue xs
  | succ k ih =>
    exact unaryValue .succ (Path.constant n k) (numeral (k+1)) (numeral k) xs
      (successorValue (Fin.cons (numeral k) Fin.elim0)) ih

theorem coordinateRecover (n : Nat) (i : Fin n) (k : Nat) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same (.projection i) (Path.constant n k)) (suc z) xs))) :
    Nonempty (Derivation body Delta (equal (xs i) (numeral k))) := by
  have he := binaryRecover InternalEqualityTest.equalityTest (.projection i)
    (Path.constant n k) (suc z) (xs i) (numeral k) xs h
    (projectionValue i xs) (constantValue n k xs)
  simpa only [equalEqn] using equalityOfAcceptance (xs i) (numeral k) he

theorem coordinateAccept (n : Nat) (i : Fin n) (k : Nat) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Delta (equal (xs i) (numeral k)))) :
    Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same (.projection i) (Path.constant n k)) (suc z) xs)) := by
  apply binaryValue InternalEqualityTest.equalityTest (.projection i)
    (Path.constant n k) (suc z) (xs i) (numeral k) xs
  · apply equalityOfEqual
    simpa only [equalEqn] using h
  · exact projectionValue i xs
  · exact constantValue n k xs

theorem contextRecover (context : Nat) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same (leftOf (.projection 0))
        (Path.constant 5 context)) (suc z) xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral context) (xs 0))) := by
  apply programCases InternalUnpair.left (Fin.cons (xs 0) Fin.elim0)
    (graph1 InternalUnpair.left (numeral context) (xs 0))
  intro β j Theta tag hj hl
  rw [graph1Rename]
  simp only [numeralRename]
  simp only [consTermRename,emptyRename] at hl
  have h' := renameInto h j Theta hj
  rw [programRename] at h'
  let ys : Fin 5 → OTerm β := fun i => (xs i).relabel j
  have hv := unaryValue InternalUnpair.left (.projection (0 : Fin 5)) tag (ys 0) ys
    hl (projectionValue 0 ys)
  have he := binaryRecover InternalEqualityTest.equalityTest (leftOf (.projection (0 : Fin 5)))
    (Path.constant 5 context) (suc z) tag (numeral context) ys h' hv
    (constantValue 5 context ys)
  have heq := equalityOfAcceptance tag (numeral context) he
  exact outputTransport InternalUnpair.left tag (numeral context) (Fin.cons (ys 0) Fin.elim0) heq hl

theorem contextAccept (context : Nat) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral context) (xs 0)))) :
    Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same (leftOf (.projection 0))
        (Path.constant 5 context)) (suc z) xs)) := by
  exact sameAccept (leftOf (.projection 0)) (Path.constant 5 context) (numeral context) xs
    (unaryValue InternalUnpair.left (.projection (0 : Fin 5)) (numeral context) (xs 0) xs
      h (projectionValue 0 xs)) (constantValue 5 context xs)

theorem typedValue (data : Data) (value typ parameter : Program 5)
    (v t p : OTerm α) (xs : Fin 5 → OTerm α)
    (hv : Nonempty (Derivation body Delta (programGraph value v xs)))
    (ht : Nonempty (Derivation body Delta (programGraph typ t xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameter p xs)))
    (h : Nonempty (Derivation body Delta (typedAccepted data v t p))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition (InternalOriginalUniformDescentSelection.selectedTyped data)
        (Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0)))) (suc z) xs)) := by
  apply compositionValue (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0))) (suc z) xs
    (Fin.cons v (Fin.cons t (Fin.cons p Fin.elim0))) h
  intro i
  exact Fin.cases hv (Fin.cases ht (Fin.cases hp (fun j => Fin.elim0 j))) i

theorem typedRecover (data : Data) (value typ parameter : Program 5)
    (v t p : OTerm α) (xs : Fin 5 → OTerm α)
    (hv : Nonempty (Derivation body Delta (programGraph value v xs)))
    (ht : Nonempty (Derivation body Delta (programGraph typ t xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameter p xs)))
    (h : Nonempty (Derivation body Delta
      (programGraph (.composition (InternalOriginalUniformDescentSelection.selectedTyped data)
        (Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0)))) (suc z) xs))) :
    Nonempty (Derivation body Delta (typedAccepted data v t p)) := by
  apply compositionRecover (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0))) (suc z) xs
    (Fin.cons v (Fin.cons t (Fin.cons p Fin.elim0))) h
  intro i
  exact Fin.cases hv (Fin.cases ht (Fin.cases hp (fun j => Fin.elim0 j))) i

theorem activeBranchRecover (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Delta (programGraph (activeBranch data) out xs))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (xs 1) (xs 2) (xs 4) (xs 3) (xs 0))) := by
  apply compositionRecover (InternalParameterizedCanonicalResultFold.actualJ data)
    (Fin.cons (.projection 1) (Fin.cons (.projection 2) (Fin.cons (.projection 4)
      (Fin.cons (.projection 3) (Fin.cons (.projection 0) Fin.elim0))))) out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4)
      (Fin.cons (xs 3) (Fin.cons (xs 0) Fin.elim0))))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j))))) i

theorem activeBranchAccept (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (xs 1) (xs 2) (xs 4) (xs 3) (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (activeBranch data) out xs)) := by
  apply compositionValue (InternalParameterizedCanonicalResultFold.actualJ data)
    (Fin.cons (.projection 1) (Fin.cons (.projection 2) (Fin.cons (.projection 4)
      (Fin.cons (.projection 3) (Fin.cons (.projection 0) Fin.elim0))))) out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4)
      (Fin.cons (xs 3) (Fin.cons (xs 0) Fin.elim0))))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j))))) i

theorem vertexRecover (data : Data) (window : Program 1) (oldVertex : Program 5)
    (xs : Fin 5 → OTerm α) (out : OTerm α)
    (ha : Nonempty (Derivation body Delta (programGraph (activation data window) (suc z) xs)))
    (h : Nonempty (Derivation body Delta (programGraph (vertex data window oldVertex) out xs))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (xs 1) (xs 2) (xs 4) (xs 3) (xs 0))) :=
  activeBranchRecover data xs out
    (successorBranchElim (activation data window) oldVertex (activeBranch data) out z xs ha h)

theorem vertexAccept (data : Data) (window : Program 1) (oldVertex : Program 5)
    (xs : Fin 5 → OTerm α) (out : OTerm α)
    (ha : Nonempty (Derivation body Delta (programGraph (activation data window) (suc z) xs)))
    (h : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (xs 1) (xs 2) (xs 4) (xs 3) (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (vertex data window oldVertex) out xs)) :=
  successorBranchIntro (activation data window) oldVertex (activeBranch data) out z xs ha
    (activeBranchAccept data xs out h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
