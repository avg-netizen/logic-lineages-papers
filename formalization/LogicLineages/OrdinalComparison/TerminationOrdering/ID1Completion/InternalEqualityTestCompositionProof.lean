module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open LogicLineages.ComputabilityKnowledge LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalEqualityTestSubtractionSupportProof InternalEqualityTestSubtractionProof
open InternalControlGraphSupportProof InternalControlGraphValueProof InternalControlGraphProof
open InternalGraphCompositionEqualityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev equalityGraph (out x y : OTerm α) : Formula α :=
  programGraph equalityTest out (Fin.cons x (Fin.cons y Fin.elim0))

@[simp] theorem equalityGraphRename {β : Type} (out x y : OTerm α) (j : α → β) :
    (equalityGraph out x y).relabel j =
      equalityGraph (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [equalityGraph,programRename,consTermRename,emptyRename]

theorem equalityTransport (out x y x' y' : OTerm α)
    (hx : Nonempty (Derivation body Gamma (eqn x x')))
    (hy : Nonempty (Derivation body Gamma (eqn y y')))
    (h : Nonempty (Derivation body Gamma (equalityGraph out x y))) :
    Nonempty (Derivation body Gamma (equalityGraph out x' y')) := by
  apply graphInputTransport body α 2 Gamma _ out (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons x' (Fin.cons y' Fin.elim0)) _ h
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · rw [onEquality]
    exact hx
  · rw [onEquality]
    exact hy

theorem reverseSubtractValue (out x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (subGraph out y x))) :
    Nonempty (Derivation body Gamma (programGraph reverseSubtract out
      (Fin.cons x (Fin.cons y Fin.elim0)))) := by
  apply compositionValue subtract
    (Fin.cons (.projection (1 : Fin 2)) (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))
    out (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons y (Fin.cons x Fin.elim0)) h
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact projectionValue (1 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))
  · exact projectionValue (0 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem reverseZeroValue (out diff x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (subGraph diff y x)))
    (hz : Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest out (Fin.cons diff Fin.elim0)))) :
    Nonempty (Derivation body Gamma (programGraph reverseZeroTest out
      (Fin.cons x (Fin.cons y Fin.elim0)))) := by
  apply compositionValue GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => reverseSubtract)
    out (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons diff Fin.elim0) hz
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact reverseSubtractValue diff x y h

theorem zeroBinaryValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma
      (programGraph zeroBinary z (Fin.cons x (Fin.cons y Fin.elim0)))) := by
  apply compositionValue .zero Fin.elim0 z (Fin.cons x (Fin.cons y Fin.elim0)) Fin.elim0
  · exact zeroValue _
  · intro i
    exact Fin.elim0 i

/-- Every intermediate graph is the unchanged arithmetic graph of the
literal child AST; no equation is substituted for a graph by definition. -/
theorem equalityFromDifferences (out forward reverse test x y : OTerm α)
    (hf : Nonempty (Derivation body Gamma (subGraph forward x y)))
    (hr : Nonempty (Derivation body Gamma (subGraph reverse y x)))
    (ht : Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest test (Fin.cons reverse Fin.elim0))))
    (hc : Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional out
      (Fin.cons forward (Fin.cons test (Fin.cons z Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (equalityGraph out x y)) := by
  apply compositionValue GorbowPRInternalControl.conditional
    (Fin.cons subtract (Fin.cons reverseZeroTest (Fin.cons zeroBinary Fin.elim0))) out
    (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons forward (Fin.cons test (Fin.cons z Fin.elim0))) hc
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i
  · exact hf
  · exact reverseZeroValue test reverse x y hr ht
  · exact zeroBinaryValue x y

theorem equalitySelf (x : OTerm α) :
    Nonempty (Derivation body Gamma (equalityGraph (suc z) x x)) :=
  equalityFromDifferences (suc z) z z (suc z) x x (subtractSelf x) (subtractSelf x)
    zeroTestZeroValue (conditionalZeroValue (suc z) z)

theorem equalityOfEqual (x y : OTerm α) (h : Nonempty (Derivation body Gamma (eqn x y))) :
    Nonempty (Derivation body Gamma (equalityGraph (suc z) x y)) :=
  equalityTransport (suc z) x x x y ⟨refl x⟩ h (equalitySelf x)

/-- Positive additive gaps in either direction force the exact output zero. -/
theorem rejectForwardGap (x y gap : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn (add x (suc gap)) y))) :
    Nonempty (Derivation body Gamma (equalityGraph z x y)) := by
  have hf := subTransport (suc gap) x (add x (suc gap)) x y
    ⟨refl x⟩ h (diagonal x (suc gap))
  have hr := subTransport z (add x (suc gap)) x y x h ⟨refl x⟩ (absorption x (suc gap))
  exact equalityFromDifferences z (suc gap) z (suc z) x y hf hr
    zeroTestZeroValue (conditionalSuccessorValue gap (suc z) z)

theorem rejectBackwardGap (x y gap : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn (add y (suc gap)) x))) :
    Nonempty (Derivation body Gamma (equalityGraph z x y)) := by
  have hf := subTransport z (add y (suc gap)) y x y h ⟨refl y⟩ (absorption y (suc gap))
  have hr := subTransport (suc gap) y (add y (suc gap)) y x
    ⟨refl y⟩ h (diagonal y (suc gap))
  exact equalityFromDifferences z z (suc gap) z x y hf hr
    (zeroTestSuccessorValue gap) (conditionalZeroValue z z)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
