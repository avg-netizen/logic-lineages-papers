module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalUnpairSupportProof InternalUnpairProof InternalUnpairArithmeticProof
open InternalUnpairReverseSyntaxProof InternalArithmeticProgramsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionEqualityProof InternalRecursionClosureLogicProof
open InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalBetaDivisionSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem addStrictCancelLeft (a s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF (add a s) (add a t)))) :
    Nonempty (Derivation body Gamma (ltF s t)) := by
  apply orderCases Gamma (add a s) (add a t) _ h
  intro β j Delta w _ ⟨he⟩
  rw [orderRename]
  simp only [addRelabel] at he
  apply actualOriginalOrderIntroduction body β Delta (s.relabel j) (t.relabel j) w
  rw [onEquality]
  exact ⟨Derivation.implicationElimination
    (leftCancellation (add (s.relabel j) (suc w)) (t.relabel j) (a.relabel j))
    (trans (symm (associativity (a.relabel j) (s.relabel j) (suc w))) he)⟩

theorem offsetBound (s r n : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn (add (square s) r) n)))
    (hi : Nonempty (Derivation body Gamma (ltF n (square (suc s))))) :
    Nonempty (Derivation body Gamma (ltF r (suc (add s s)))) := by
  obtain ⟨he⟩ := he
  obtain ⟨hi⟩ := hi
  have h0 := orderLeft (square (suc s)) (symm he) hi
  have h1 := orderRight (add (square s) r) (successorSquareExpansion s) h0
  exact addStrictCancelLeft (square s) r (suc (add s s)) ⟨h1⟩

theorem componentNotLess (s t r : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn (add s t) r)))
    (hb : Nonempty (Derivation body Gamma (ltF r (suc (add s s))))) :
    Nonempty (Derivation body Gamma (ltF s t).not) := by
  obtain ⟨he⟩ := he
  obtain ⟨hb⟩ := hb
  let Delta := ltF s t :: Gamma
  obtain ⟨ha⟩ := addStrictLeft (body := body) (Gamma := Delta) s s t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc := strictWeakTrans (add s s) r (add s s)
    ⟨orderRight (add s s) (addHyp he _) ha⟩ ⟨addHyp hb _⟩
  obtain ⟨hc⟩ := hc
  obtain ⟨irr⟩ := actualOriginalOrderIrreflexivity body α (add s s)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (weakenClosed irr Delta) hc)⟩

/-- An actual pair witness determines the supplied coordinate graph outputs
by the already accepted generated-code inverse and original functionality. -/
theorem pairFromKnownCoordinates (n x y u v : OTerm α)
    (hx : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left x n)))
    (hy : Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right y n)))
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing n u v))) :
    Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing n x y)) := by
  obtain ⟨hu⟩ := closedApply (actualOriginalGeneratedCodeInverse body α n u v) hp
  have ex := valueUnique InternalUnpair.left u x (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionLeft hu⟩ hx
  have ey := valueUnique InternalUnpair.right v y (Fin.cons n Fin.elim0)
    ⟨Derivation.conjunctionRight hu⟩ hy
  apply graphInputTransport body α 2 Gamma (OrdinaryArithmetic.graphFormula InternalPairing.pairing)
    n (Fin.cons u (Fin.cons v Fin.elim0)) (Fin.cons x (Fin.cons y Fin.elim0)) _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]
    exact ex
  · rw [onEquality]
    exact ey

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSupportProof
