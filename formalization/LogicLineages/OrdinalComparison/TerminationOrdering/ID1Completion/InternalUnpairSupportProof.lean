module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalUnpair
open InternalControlGraphSupportProof InternalArithmeticProgramsMultiplicationProof
open InternalArithmeticProgramsSupportProof InternalEqualityTestSubtractionSupportProof
open InternalTagArithmeticSyntaxProof InternalMultiplicationLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev unaryGraph (p : Program 1) (out n : OTerm α) : Formula α :=
  programGraph p out (Fin.cons n Fin.elim0)

theorem rootSquareValue (n s : OTerm α)
    (hs : Nonempty (Derivation body Gamma (unaryGraph InternalSquareRoot.root s n))) :
    Nonempty (Derivation body Gamma (unaryGraph rootSquare (mul s s) n)) := by
  apply compositionValue InternalArithmeticPrograms.multiplication
    (Fin.cons InternalSquareRoot.root (Fin.cons InternalSquareRoot.root Fin.elim0))
    (mul s s) (Fin.cons n Fin.elim0) (Fin.cons s (Fin.cons s Fin.elim0)) (multiplicationValue s s)
  intro i
  exact Fin.cases hs (Fin.cases hs (fun k => Fin.elim0 k)) i

theorem residualValue (n s r : OTerm α)
    (hs : Nonempty (Derivation body Gamma (unaryGraph InternalSquareRoot.root s n)))
    (hr : Nonempty (Derivation body Gamma (subGraph r (mul s s) n))) :
    Nonempty (Derivation body Gamma (unaryGraph residual r n)) := by
  apply compositionValue InternalEqualityTest.subtract
    (Fin.cons rootSquare (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))
    r (Fin.cons n Fin.elim0) (Fin.cons (mul s s) (Fin.cons n Fin.elim0)) hr
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · exact rootSquareValue n s hs
  · exact projectionValue (0 : Fin 1) (Fin.cons n Fin.elim0)

theorem residualBelowRootValue (n s r c : OTerm α)
    (hs : Nonempty (Derivation body Gamma (unaryGraph InternalSquareRoot.root s n)))
    (hr : Nonempty (Derivation body Gamma (unaryGraph residual r n)))
    (hc : Nonempty (Derivation body Gamma (InternalLessThanSupportProof.lessGraph c r s))) :
    Nonempty (Derivation body Gamma (unaryGraph residualBelowRoot c n)) := by
  apply compositionValue InternalLessThan.ltTest
    (Fin.cons residual (Fin.cons InternalSquareRoot.root Fin.elim0))
    c (Fin.cons n Fin.elim0) (Fin.cons r (Fin.cons s Fin.elim0)) hc
  intro i
  exact Fin.cases hr (Fin.cases hs (fun k => Fin.elim0 k)) i

theorem residualMinusRootValue (n s r out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (unaryGraph InternalSquareRoot.root s n)))
    (hr : Nonempty (Derivation body Gamma (unaryGraph residual r n)))
    (hd : Nonempty (Derivation body Gamma (subGraph out s r))) :
    Nonempty (Derivation body Gamma (unaryGraph residualMinusRoot out n)) := by
  apply compositionValue InternalEqualityTest.subtract
    (Fin.cons InternalSquareRoot.root (Fin.cons residual Fin.elim0))
    out (Fin.cons n Fin.elim0) (Fin.cons s (Fin.cons r Fin.elim0)) hd
  intro i
  exact Fin.cases hs (Fin.cases hr (fun k => Fin.elim0 k)) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairSupportProof
