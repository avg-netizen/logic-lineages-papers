module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseReconstructionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalUnpairSupportProof InternalUnpairArithmeticProof InternalUnpairReverseSyntaxProof
open InternalUnpairReverseSupportProof InternalArithmeticProgramsSupportProof InternalPairingSupportProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalBetaTotalityProof InternalBetaDivisionSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Every original square interval has a pair preimage, which the accepted
coordinate inverse identifies with the given coordinate witnesses. -/
theorem reconstructOffset (n s r x y : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn (add (square s) r) n)))
    (hb : Nonempty (Derivation body Gamma (ltF r (suc (add s s)))))
    (hx : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left x n)))
    (hy : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right y n))) :
    Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing n x y)) := by
  obtain ⟨he⟩ := he
  obtain ⟨hb⟩ := hb
  obtain ⟨hx⟩ := hx
  obtain ⟨hy⟩ := hy
  let psi := binaryGraph InternalPairing.pairing n x y
  have hl : Nonempty (Derivation body (ltF r s :: Gamma) psi) := by
    have hp := pairingOfLess (body := body) (Gamma := ltF r s :: Gamma) r s
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := outputTransport InternalPairing.pairing (add (square s) r) n
      (Fin.cons r (Fin.cons s Fin.elim0)) ⟨addHyp he _⟩ hp
    exact pairFromKnownCoordinates n x y r s ⟨addHyp hx _⟩ ⟨addHyp hy _⟩ hp
  have hn : Nonempty (Derivation body ((ltF r s).not :: Gamma) psi) := by
    let Gamma0 := (ltF r s).not :: Gamma
    apply weakOrderCases Gamma0 s r psi
      (notLessWeak r s ⟨Derivation.hypothesis List.mem_cons_self⟩)
    intro β j Delta t hj ⟨hr⟩
    simp only [psi,binaryGraphRename]
    have he' := renameInto ⟨addHyp he (ltF r s).not⟩ j Delta hj
    have hb' := renameInto ⟨addHyp hb (ltF r s).not⟩ j Delta hj
    have hx' := renameInto ⟨addHyp hx (ltF r s).not⟩ j Delta hj
    have hy' := renameInto ⟨addHyp hy (ltF r s).not⟩ j Delta hj
    simp only [eqnRelabel,addRelabel,square,mulRelabel] at he'
    simp only [orderRename,sucRelabel,addRelabel] at hb'
    simp only [unaryGraphRename] at hx' hy'
    have hn' := componentNotLess (s.relabel j) t (r.relabel j) ⟨hr⟩ hb'
    have hp := pairingOfNotLess (s.relabel j) t hn'
    obtain ⟨he'⟩ := he'
    have outEq : Nonempty (Derivation body Delta
        (eqn (add (add (square (s.relabel j)) (s.relabel j)) t) (n.relabel j))) :=
      ⟨trans (associativity (square (s.relabel j)) (s.relabel j) t)
        (trans (congAddLeft (square (s.relabel j)) hr) he')⟩
    have hp := outputTransport InternalPairing.pairing
      (add (add (square (s.relabel j)) (s.relabel j)) t) (n.relabel j)
      (Fin.cons (s.relabel j) (Fin.cons t Fin.elim0)) outEq hp
    exact pairFromKnownCoordinates (n.relabel j) (x.relabel j) (y.relabel j)
      (s.relabel j) t hx' hy' hp
  obtain ⟨hl⟩ := hl
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle (ltF r s))
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hn)⟩

theorem reconstructInterval (n s x y : OTerm α)
    (hi : Nonempty (Derivation body Gamma (interval s n)))
    (hx : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left x n)))
    (hy : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right y n))) :
    Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing n x y)) := by
  obtain ⟨hi⟩ := hi
  apply weakOrderCases Gamma (square s) n _ ⟨Derivation.conjunctionLeft hi⟩
  intro β j Delta r hj ⟨he⟩
  rw [binaryGraphRename]
  simp only [square,mulRelabel] at he
  have upper := renameInto ⟨Derivation.conjunctionRight hi⟩ j Delta hj
  simp only [orderRename,square,mulRelabel,sucRelabel] at upper
  have hx' := renameInto hx j Delta hj
  have hy' := renameInto hy j Delta hj
  simp only [unaryGraphRename] at hx' hy'
  exact reconstructOffset (n.relabel j) (s.relabel j) r (x.relabel j) (y.relabel j)
    ⟨he⟩ (offsetBound (s.relabel j) r (n.relabel j) ⟨he⟩ upper) hx' hy'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseReconstructionProof
