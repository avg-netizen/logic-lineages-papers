module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalLessThan
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptance InternalAcceptanceBranchProof InternalControlGraphSupportProof
open InternalEqualityTestSubtractionSupportProof InternalEqualityTestSubtractionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalAdditionLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev lessGraph (out x y : OTerm α) : Formula α :=
  programGraph ltTest out (Fin.cons x (Fin.cons y Fin.elim0))

@[simp] theorem lessGraphRename {β : Type} (out x y : OTerm α) (j : α → β) :
    (lessGraph out x y).relabel j =
      lessGraph (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [lessGraph,programRename,consTermRename,emptyRename]

theorem zeroConstantValue {n : Nat} (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (constantZero n) z xs)) := by
  apply compositionValue .zero Fin.elim0 z xs Fin.elim0 (zeroValue _)
  intro i
  exact Fin.elim0 i

theorem oneConstantValue {n : Nat} (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (constantOne n) (suc z) xs)) := by
  apply compositionValue .succ (fun _ : Fin 1 => constantZero n) (suc z) xs
    (Fin.cons z Fin.elim0) (successorValue (Fin.cons z Fin.elim0))
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact zeroConstantValue xs

theorem rejectOfZeroDifference (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (subGraph z x y))) :
    Nonempty (Derivation body Gamma (lessGraph z x y)) :=
  zeroBranchIntro InternalEqualityTest.subtract (constantZero 2) (constantOne 2) z
    (Fin.cons x (Fin.cons y Fin.elim0)) h (zeroConstantValue _)

theorem acceptOfGap (x y gap : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn (add x (suc gap)) y))) :
    Nonempty (Derivation body Gamma (lessGraph (suc z) x y)) := by
  have hd := subTransport (suc gap) x (add x (suc gap)) x y
    ⟨refl x⟩ h (diagonal x (suc gap))
  exact successorBranchIntro InternalEqualityTest.subtract (constantZero 2) (constantOne 2)
    (suc z) gap (Fin.cons x (Fin.cons y Fin.elim0)) hd (oneConstantValue _)

theorem acceptOfLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma (lessGraph (suc z) x y)) := by
  apply orderCases Gamma x y _ h
  intro β j Delta gap _ he
  simp only [lessGraphRename,sucRelabel,zRelabel]
  exact acceptOfGap (x.relabel j) (y.relabel j) gap he

theorem rejectOfEqual (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (eqn x y))) :
    Nonempty (Derivation body Gamma (lessGraph z x y)) :=
  rejectOfZeroDifference x y (subTransport z x x x y ⟨refl x⟩ h (subtractSelf x))

theorem rejectOfGreater (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF y x))) :
    Nonempty (Derivation body Gamma (lessGraph z x y)) := by
  apply orderCases Gamma y x _ h
  intro β j Delta gap _ he
  simp only [lessGraphRename,zRelabel]
  exact rejectOfZeroDifference (x.relabel j) (y.relabel j)
    (subTransport z (add (y.relabel j) (suc gap)) (y.relabel j)
      (x.relabel j) (y.relabel j) he ⟨refl _⟩ (absorption (y.relabel j) (suc gap)))

/-- The actual internally proved trichotomy eliminates the forbidden strict
case. Equality and reverse strict order give zero by subtraction laws. -/
theorem rejectOfNotLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma (lessGraph z x y)) := by
  obtain ⟨h⟩ := h
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Gamma)
  have hl : Derivation body Gamma ((ltF x y).imp (lessGraph z x y)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp h _) (Derivation.hypothesis List.mem_cons_self)))
  obtain ⟨he⟩ := rejectOfEqual (body := body) (Gamma := eqn x y :: Gamma) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := rejectOfGreater (body := body) (Gamma := ltF y x :: Gamma) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hrest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp (lessGraph z x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc hl hrest⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
