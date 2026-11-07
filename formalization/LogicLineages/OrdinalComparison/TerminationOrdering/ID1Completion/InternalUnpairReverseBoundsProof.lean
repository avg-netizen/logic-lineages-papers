module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalUnpairReverse
open InternalUnpairSupportProof InternalArithmeticProgramsSupportProof InternalPairingSupportProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof InternalUnpairReverseProof
open InternalUnpairReverseBoundsArithmeticProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof InternalBetaTotalityProof

theorem actualOriginalPairingCoordinateBounds : InternalUnpairReverseTargets.ActualOriginalPairingCoordinateBounds := by
  intro body α n x y
  let g := binaryGraph InternalPairing.pairing n x y
  let psi := coordinateBounds n x y
  have hl : Nonempty (Derivation body (ltF x y :: [g]) psi) := by
    let Gamma := ltF x y :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing n (add (mul y y) x)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfLess x y hc)
    obtain ⟨hb⟩ := lessBranchBounds (body := body) (Gamma := Gamma) x y
    exact ⟨boundsTransport x y (symm he) hb⟩
  have hn : Nonempty (Derivation body ((ltF x y).not :: [g]) psi) := by
    let Gamma := (ltF x y).not :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing n (add (add (mul x x) x) y)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfNotLess x y hc)
    obtain ⟨hb⟩ := nonLessBranchBounds (body := body) (Gamma := Gamma) x y
    exact ⟨boundsTransport x y (symm he) hb⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination (excludedMiddle (ltF x y))
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hn))⟩

theorem actualOriginalUnpairCoordinateBounds : InternalUnpairReverseTargets.ActualOriginalUnpairCoordinateBounds := by
  intro body α n x y
  let premise := unaryGraph InternalUnpair.left x n ⊓ unaryGraph InternalUnpair.right y n
  have hp : Nonempty (Derivation body [premise] (binaryGraph InternalPairing.pairing n x y)) :=
    closedApply (actualOriginalUnpairReverseInverse body α n x y)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := closedApply (actualOriginalPairingCoordinateBounds body α n x y) hp
  exact ⟨Derivation.implicationIntroduction hb⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsProof
