module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalArithmeticProgramsSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalUnpairReverseSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalOriginalPairingOrderArithmeticProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonProof InternalBetaTotalityProof InternalControlGraphSupportProof
open InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof
open InternalPairingSumBoundsArithmeticProof InternalPairingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Strict monotonicity of the actual original pairing in its right coordinate.
Every branch is discharged in the object calculus. -/
theorem rightStrict (x y v p q : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (hq : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing q x v)))
    (hs : Nonempty (Derivation body Gamma (ltF y v))) :
    Nonempty (Derivation body Gamma (ltF p q)) := by
  apply formulaCases (ltF x y) _
  · apply formulaCases (ltF x v) _
    · have hy : Nonempty (Derivation body (ltF x v :: ltF x y :: Gamma) (ltF x y)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hv : Nonempty (Derivation body (ltF x v :: ltF x y :: Gamma) (ltF x v)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp (ltF x y)) (ltF x v)
      have hq := withHyp (withHyp hq (ltF x y)) (ltF x v)
      have hs := withHyp (withHyp hs (ltF x y)) (ltF x v)
      exact strictTransport p q (add (square y) x) (add (square v) x)
        (lessValue p x y hp hy) (lessValue q x v hq hv)
        (addStrictRight (square y) (square v) x (squareStrictMonotonicity y v hs))
    · have hy : Nonempty (Derivation body ((ltF x v).not :: ltF x y :: Gamma) (ltF x y)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hv : Nonempty (Derivation body ((ltF x v).not :: ltF x y :: Gamma) ((ltF x v).not)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp (ltF x y)) ((ltF x v).not)
      have hq := withHyp (withHyp hq (ltF x y)) ((ltF x v).not)
      have hs := withHyp (withHyp hs (ltF x y)) ((ltF x v).not)
      obtain ⟨hc⟩ := strictTrans x y v hy hs
      obtain ⟨hv⟩ := hv
      exact ⟨Derivation.explosion (Derivation.implicationElimination hv hc)⟩
  · apply formulaCases (ltF x v) _
    · have hy : Nonempty (Derivation body (ltF x v :: (ltF x y).not :: Gamma) ((ltF x y).not)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hv : Nonempty (Derivation body (ltF x v :: (ltF x y).not :: Gamma) (ltF x v)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp ((ltF x y).not)) (ltF x v)
      have hq := withHyp (withHyp hq ((ltF x y).not)) (ltF x v)
      have hs := withHyp (withHyp hs ((ltF x y).not)) (ltF x v)
      exact strictTransport p q (add (add (square x) x) y) (add (square v) x)
        (nonLessValue p x y hp hy) (lessValue q x v hq hv) (rightCrossing x y v hy hv)
    · have hy : Nonempty (Derivation body ((ltF x v).not :: (ltF x y).not :: Gamma) ((ltF x y).not)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hv : Nonempty (Derivation body ((ltF x v).not :: (ltF x y).not :: Gamma) ((ltF x v).not)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp ((ltF x y).not)) ((ltF x v).not)
      have hq := withHyp (withHyp hq ((ltF x y).not)) ((ltF x v).not)
      have hs := withHyp (withHyp hs ((ltF x y).not)) ((ltF x v).not)
      exact strictTransport p q (add (add (square x) x) y) (add (add (square x) x) v)
        (nonLessValue p x y hp hy) (nonLessValue q x v hq hv)
        (addStrictLeft (add (square x) x) y v hs)

/-- Weak monotonicity of the actual original pairing in its left coordinate. -/
theorem leftWeak (x u y p q : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (hq : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing q u y)))
    (hs : Nonempty (Derivation body Gamma (ltF x (suc u)))) :
    Nonempty (Derivation body Gamma (ltF p (suc q))) := by
  apply formulaCases (ltF x y) _
  · apply formulaCases (ltF u y) _
    · have hx : Nonempty (Derivation body (ltF u y :: ltF x y :: Gamma) (ltF x y)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hu : Nonempty (Derivation body (ltF u y :: ltF x y :: Gamma) (ltF u y)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp (ltF x y)) (ltF u y)
      have hq := withHyp (withHyp hq (ltF x y)) (ltF u y)
      have hs := withHyp (withHyp hs (ltF x y)) (ltF u y)
      exact weakTransport p q (add (square y) x) (add (square y) u)
        (lessValue p x y hp hx) (lessValue q u y hq hu) (addWeakLeft (square y) x u hs)
    · have hx : Nonempty (Derivation body ((ltF u y).not :: ltF x y :: Gamma) (ltF x y)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hu : Nonempty (Derivation body ((ltF u y).not :: ltF x y :: Gamma) ((ltF u y).not)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp (ltF x y)) ((ltF u y).not)
      have hq := withHyp (withHyp hq (ltF x y)) ((ltF u y).not)
      have hs := withHyp (withHyp hs (ltF x y)) ((ltF u y).not)
      exact weakTransport p q (add (square y) x) (add (add (square u) u) y)
        (lessValue p x y hp hx) (nonLessValue q u y hq hu)
        (weakTrans _ (add (square u) u) _
          (addWeakBoth (square y) (square u) x u (squareWeak y u (notLessWeak u y hu)) hs)
          (leftWeakAdd (add (square u) u) y))
  · apply formulaCases (ltF u y) _
    · have hx : Nonempty (Derivation body (ltF u y :: (ltF x y).not :: Gamma) ((ltF x y).not)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hu : Nonempty (Derivation body (ltF u y :: (ltF x y).not :: Gamma) (ltF u y)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp ((ltF x y).not)) (ltF u y)
      have hq := withHyp (withHyp hq ((ltF x y).not)) (ltF u y)
      have hs := withHyp (withHyp hs ((ltF x y).not)) (ltF u y)
      obtain ⟨hc⟩ := weakStrictTrans x u y hs hu
      obtain ⟨hx⟩ := hx
      exact ⟨Derivation.explosion (Derivation.implicationElimination hx hc)⟩
    · have hx : Nonempty (Derivation body ((ltF u y).not :: (ltF x y).not :: Gamma) ((ltF x y).not)) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have hu : Nonempty (Derivation body ((ltF u y).not :: (ltF x y).not :: Gamma) ((ltF u y).not)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hp := withHyp (withHyp hp ((ltF x y).not)) ((ltF u y).not)
      have hq := withHyp (withHyp hq ((ltF x y).not)) ((ltF u y).not)
      have hs := withHyp (withHyp hs ((ltF x y).not)) ((ltF u y).not)
      exact weakTransport p q (add (add (square x) x) y) (add (add (square u) u) y)
        (nonLessValue p x y hp hx) (nonLessValue q u y hq hu)
        (addWeakRight (add (square x) x) (add (square u) u) y
          (addWeakBoth (square x) (square u) x u (squareWeak x u hs) hs))

theorem rightWeak (x y v p q : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (hq : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing q x v)))
    (hs : Nonempty (Derivation body Gamma (ltF y (suc v)))) :
    Nonempty (Derivation body Gamma (ltF p (suc q))) := by
  apply weakCases y v _ hs
  · exact rightSuccessor p q (rightStrict x y v p q (withHyp hp _) (withHyp hq _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · obtain ⟨he⟩ := valueUnique InternalPairing.pairing p q
      (Fin.cons x (Fin.cons v Fin.elim0))
      (InternalGraphCompositionEqualityProof.graphInputTransport body α 2 (eqn y v :: Gamma)
        (OrdinaryArithmetic.graphFormula InternalPairing.pairing) p
        (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons x (Fin.cons v Fin.elim0))
        (by
          intro i
          rw [onEquality]
          exact Fin.cases (show Nonempty (Derivation body (eqn y v :: Gamma) (eqn x x)) from ⟨refl x⟩)
            (Fin.cases ⟨Derivation.hypothesis List.mem_cons_self⟩ (fun k => Fin.elim0 k)) i)
        (withHyp hp _))
      (withHyp hq _)
    exact ⟨equalToNext he⟩

/-- Both coordinates are monotone. The intermediate pair output is obtained
from original Program totality and eliminated inside the arithmetic calculus. -/
theorem bothWeak (x u y v p q : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (hq : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing q u v)))
    (hx : Nonempty (Derivation body Gamma (ltF x (suc u))))
    (hy : Nonempty (Derivation body Gamma (ltF y (suc v)))) :
    Nonempty (Derivation body Gamma (ltF p (suc q))) := by
  apply programCases InternalPairing.pairing (Fin.cons u (Fin.cons y Fin.elim0)) _
  intro β j Delta middle hj hm
  simp only [orderRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hm
  have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Delta hj
  have hq' := InternalGraphCompositionFunctionalityProof.renameInto hq j Delta hj
  rw [binaryGraphRename] at hp' hq'
  have hx' := InternalGraphCompositionFunctionalityProof.renameInto hx j Delta hj
  have hy' := InternalGraphCompositionFunctionalityProof.renameInto hy j Delta hj
  simp only [orderRename,sucRelabel] at hx' hy'
  exact weakTrans (p.relabel j) middle (q.relabel j)
    (leftWeak (x.relabel j) (u.relabel j) (y.relabel j) (p.relabel j) middle hp' hm hx')
    (rightWeak (u.relabel j) (y.relabel j) (v.relabel j) middle (q.relabel j) hm hq' hy')

/-- Same-left order reflection follows by internal trichotomy and strict
right-coordinate monotonicity, not by interpreting the codes as naturals. -/
theorem rightReflect (x y v p q : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (hq : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing q x v)))
    (hs : Nonempty (Derivation body Gamma (ltF p (suc q)))) :
    Nonempty (Derivation body Gamma (ltF y (suc v))) := by
  have hn : Nonempty (Derivation body Gamma (ltF v y).not) := by
    obtain ⟨bad⟩ := strictWeakConflict q p (⊥ : Formula α)
      (rightStrict x v y q p (withHyp hq _) (withHyp hp _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hs _)
    exact ⟨Derivation.implicationIntroduction bad⟩
  exact notLessWeak v y hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof.rightStrict
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof.leftWeak
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof.rightWeak
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof.rightReflect

#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof.bothWeak
