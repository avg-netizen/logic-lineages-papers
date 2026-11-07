module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalUnpair InternalUnpairSupportProof InternalUnpairArithmeticProof
open InternalSquareRootArithmetic InternalSquareRootProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalLessThanSupportProof
open InternalEqualityTestSubtractionSupportProof InternalEqualityTestSubtractionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof
open InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rootOfInterval (s n : OTerm α)
    (h : Nonempty (Derivation body Gamma (interval s n))) :
    Nonempty (Derivation body Gamma (unaryGraph InternalSquareRoot.root s n)) := by
  obtain ⟨d⟩ := actualOriginalSquareRootGraph body α s n
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed (Derivation.conjunctionRight d) Gamma) h⟩

/-- Both coordinates on the original strict pair branch. -/
theorem unpairOfLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma
      (unaryGraph InternalUnpair.left x (add (mul y y) x) ⊓
       unaryGraph InternalUnpair.right y (add (mul y y) x))) := by
  let n := add (mul y y) x
  have hs := rootOfInterval y n (lessPairInterval x y h)
  have hr := residualValue n y x hs (diagonal (mul y y) x)
  have hc := residualBelowRootValue n y x (suc z) hs hr (acceptOfLess x y h)
  obtain ⟨hl⟩ := successorBranchIntro residualBelowRoot InternalSquareRoot.root residual x z
    (Fin.cons n Fin.elim0) hc hr
  obtain ⟨hh⟩ := successorBranchIntro residualBelowRoot residualMinusRoot InternalSquareRoot.root y z
    (Fin.cons n Fin.elim0) hc hs
  exact ⟨Derivation.conjunctionIntroduction hl hh⟩

/-- Both coordinates on the original non-strict pair branch. -/
theorem unpairOfNotLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma
      (unaryGraph InternalUnpair.left x (add (add (mul x x) x) y) ⊓
       unaryGraph InternalUnpair.right y (add (add (mul x x) x) y))) := by
  let n := add (add (mul x x) x) y
  have hs := rootOfInterval x n (nonLessPairInterval x y h)
  have hd : Nonempty (Derivation body Gamma (subGraph (add x y) (mul x x) n)) :=
    subTransport (add x y) (mul x x) (add (mul x x) (add x y)) (mul x x) n
      ⟨refl _⟩ ⟨symm (associativity (mul x x) x y)⟩ (diagonal (mul x x) (add x y))
  have hr := residualValue n x (add x y) hs hd
  have hc := residualBelowRootValue n x (add x y) z hs hr (rejectOfNotLess (add x y) x (notLessSum x y))
  have hm := residualMinusRootValue n x (add x y) y hs hr (diagonal x y)
  obtain ⟨hl⟩ := zeroBranchIntro residualBelowRoot InternalSquareRoot.root residual x
    (Fin.cons n Fin.elim0) hc hs
  obtain ⟨hh⟩ := zeroBranchIntro residualBelowRoot residualMinusRoot InternalSquareRoot.root y
    (Fin.cons n Fin.elim0) hc hm
  exact ⟨Derivation.conjunctionIntroduction hl hh⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairBranchProof
