module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalListCodec
open InternalListCodecSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalEqualityTestPredecessorProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem nonzeroRename {β : Type} (n : OTerm α) (j : α → β) :
    ((eqn n z).not).relabel j = (eqn (n.relabel j) z).not := by
  change ((eqn n z).relabel j).not = _
  rw [eqnRelabel,zRelabel]

/-- The exceptional predecessor-zero disjunct is rejected internally using the
explicit nonzero premise; no meta-level case split on the input is used. -/
theorem predecessorAtNonzero (n p : OTerm α)
    (hn : Nonempty (Derivation body Gamma (eqn n z).not))
    (hp : Nonempty (Derivation body Gamma (unaryGraph InternalEqualityTest.predecessor p n))) :
    Nonempty (Derivation body Gamma (eqn n (suc p))) := by
  obtain ⟨hn⟩ := hn
  obtain ⟨hd⟩ := predecessorForward p n hp
  simp only [InternalEqualityTest.predecessorSpec,equalEqn] at hd
  let zeroCase := (eqn n z) ⊓ (eqn p z)
  have hz : Derivation body (zeroCase :: Gamma) (eqn n (suc p)) :=
    Derivation.explosion (Derivation.implicationElimination (addHyp hn _)
      (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))
  have hs : Derivation body (eqn n (suc p) :: Gamma) (eqn n (suc p)) :=
    Derivation.hypothesis List.mem_cons_self
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hz)
    (Derivation.implicationIntroduction hs)⟩

theorem headRecover (n p h : OTerm α)
    (hp : Nonempty (Derivation body Gamma (unaryGraph InternalEqualityTest.predecessor p n)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode h n))) :
    Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left h p)) := by
  apply compositionRecover InternalUnpair.left (fun _ : Fin 1 => InternalEqualityTest.predecessor)
    h (Fin.cons n Fin.elim0) (Fin.cons p Fin.elim0) hh
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact hp

theorem tailRecover (n p t : OTerm α)
    (hp : Nonempty (Derivation body Gamma (unaryGraph InternalEqualityTest.predecessor p n)))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode t n))) :
    Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right t p)) := by
  apply compositionRecover InternalUnpair.right (fun _ : Fin 1 => InternalEqualityTest.predecessor)
    t (Fin.cons n Fin.elim0) (Fin.cons p Fin.elim0) ht
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact hp

theorem reconstructAtPredecessor (n p h t : OTerm α)
    (hn : Nonempty (Derivation body Gamma (eqn n z).not))
    (hp : Nonempty (Derivation body Gamma (unaryGraph InternalEqualityTest.predecessor p n)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode h n)))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode t n))) :
    Nonempty (Derivation body Gamma (consGraph n h t)) := by
  obtain ⟨he⟩ := predecessorAtNonzero n p hn hp
  obtain ⟨hl⟩ := headRecover n p h hp hh
  obtain ⟨hr⟩ := tailRecover n p t hp ht
  have pair := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body α p h t)
    (show Nonempty (Derivation body Gamma
      ((unaryGraph InternalUnpair.left h p) ⊓ (unaryGraph InternalUnpair.right t p))) from
      ⟨Derivation.conjunctionIntroduction hl hr⟩)
  exact outputTransport consCode (suc p) n (Fin.cons h (Fin.cons t Fin.elim0))
    ⟨symm he⟩ (consValue p h t pair)

theorem reconstructNonzero (n h t : OTerm α)
    (hn : Nonempty (Derivation body Gamma (eqn n z).not))
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode h n)))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode t n))) :
    Nonempty (Derivation body Gamma (consGraph n h t)) := by
  apply programCases InternalEqualityTest.predecessor (Fin.cons n Fin.elim0) _
  intro β j Delta p hj hp
  rw [consGraphRename]
  simp only [consTermRename,emptyRename] at hp
  have hn' := renameInto hn j Delta hj
  rw [nonzeroRename] at hn'
  have hh' := renameInto hh j Delta hj
  have ht' := renameInto ht j Delta hj
  rw [unaryGraphRename] at hh' ht'
  exact reconstructAtPredecessor (n.relabel j) p (h.relabel j) (t.relabel j) hn' hp hh' ht'

theorem consTailAtPair (n p h t : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph n h t)))
    (hp : Nonempty (Derivation body Gamma (pairGraph p h t))) :
    Nonempty (Derivation body Gamma (ltF t n)) := by
  obtain ⟨he⟩ := valueUnique consCode n (suc p) (Fin.cons h (Fin.cons t Fin.elim0))
    hc (consValue p h t hp)
  obtain ⟨hb⟩ := closedApply
    (InternalUnpairReverseBoundsProof.actualOriginalPairingCoordinateBounds body α p h t) hp
  exact ⟨orderRight t (symm he) (Derivation.conjunctionRight hb)⟩

theorem consTailDescent (n h t : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph n h t))) :
    Nonempty (Derivation body Gamma (ltF t n)) := by
  apply programCases InternalPairing.pairing (Fin.cons h (Fin.cons t Fin.elim0)) _
  intro β j Delta p hj hp
  rw [orderRename]
  simp only [consTermRename,emptyRename] at hp
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  exact consTailAtPair (n.relabel j) p (h.relabel j) (t.relabel j) hc' hp

/-- A head witness is supplied internally by totality, not assumed in the
nonzero tail-descent target. -/
theorem nonzeroTailDescent (n t : OTerm α)
    (hn : Nonempty (Derivation body Gamma (eqn n z).not))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode t n))) :
    Nonempty (Derivation body Gamma (ltF t n)) := by
  apply programCases headCode (Fin.cons n Fin.elim0) _
  intro β j Delta h hj hh
  rw [orderRename]
  simp only [consTermRename,emptyRename] at hh
  have hn' := renameInto hn j Delta hj
  rw [nonzeroRename] at hn'
  have ht' := renameInto ht j Delta hj
  rw [unaryGraphRename] at ht'
  exact consTailDescent (n.relabel j) h (t.relabel j)
    (reconstructNonzero (n.relabel j) h (t.relabel j) hn' hh ht')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
