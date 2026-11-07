module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalUnpairSupportProof InternalUnpairBranchProof InternalPairingSupportProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof InternalArithmeticProgramsSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof InternalBetaTotalityProof
open InternalRecursionClosureProof

/-- The generated-code inverse is proved in the original object calculus.
This proof imports no evaluation calibration and no semantic reflection rule. -/
theorem actualOriginalGeneratedCodeInverse : InternalUnpairTargets.ActualOriginalGeneratedCodeInverse := by
  intro body α p x y
  let g := binaryGraph InternalPairing.pairing p x y
  let psi := unaryGraph InternalUnpair.left x p ⊓ unaryGraph InternalUnpair.right y p
  have hl : Nonempty (Derivation body (ltF x y :: [g]) psi) := by
    let Gamma := ltF x y :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing p (add (mul y y) x)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfLess x y hc)
    obtain ⟨hu⟩ := unpairOfLess x y hc
    obtain ⟨left⟩ := headTransport InternalUnpair.left x (add (mul y y) x) p Fin.elim0
      ⟨symm he⟩ ⟨Derivation.conjunctionLeft hu⟩
    obtain ⟨right⟩ := headTransport InternalUnpair.right y (add (mul y y) x) p Fin.elim0
      ⟨symm he⟩ ⟨Derivation.conjunctionRight hu⟩
    exact ⟨Derivation.conjunctionIntroduction left right⟩
  have hn : Nonempty (Derivation body ((ltF x y).not :: [g]) psi) := by
    let Gamma := (ltF x y).not :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing p (add (add (mul x x) x) y)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfNotLess x y hc)
    obtain ⟨hu⟩ := unpairOfNotLess x y hc
    obtain ⟨left⟩ := headTransport InternalUnpair.left x (add (add (mul x x) x) y) p Fin.elim0
      ⟨symm he⟩ ⟨Derivation.conjunctionLeft hu⟩
    obtain ⟨right⟩ := headTransport InternalUnpair.right y (add (add (mul x x) x) y) p Fin.elim0
      ⟨symm he⟩ ⟨Derivation.conjunctionRight hu⟩
    exact ⟨Derivation.conjunctionIntroduction left right⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination (excludedMiddle (ltF x y))
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hn))⟩

theorem actualOriginalUnpairTotalFunctional : InternalUnpairTargets.ActualOriginalUnpairTotalFunctional :=
  fun body => ⟨actualOriginalPrograms body 1 InternalUnpair.left,
    actualOriginalPrograms body 1 InternalUnpair.right⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
