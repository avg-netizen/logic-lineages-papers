module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseReconstructionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalUnpairSupportProof InternalArithmeticProgramsSupportProof InternalUnpairReverseSyntaxProof
open InternalUnpairReverseReconstructionProof InternalSquareRootSyntaxProof InternalSquareRootProof
open InternalOriginalOrderProof

theorem actualOriginalUnpairReverseInverse : InternalUnpairReverseTargets.ActualOriginalUnpairReverseInverse := by
  intro body α n x y
  let premise := unaryGraph InternalUnpair.left x n ⊓ unaryGraph InternalUnpair.right y n
  let Gamma := [premise]
  have hx : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left x n)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hy : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right y n)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  have result : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing n x y)) := by
    apply certifiedCases Gamma n _ (certifiedValue n)
    intro β j Delta s hj _ hi
    rw [binaryGraphRename]
    have hx' := renameInto hx j Delta hj
    have hy' := renameInto hy j Delta hj
    simp only [unaryGraphRename] at hx' hy'
    exact reconstructInterval (n.relabel j) s (x.relabel j) (y.relabel j) hi hx' hy'
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
