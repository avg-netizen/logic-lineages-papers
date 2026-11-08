module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalPairingSumBounds
open InternalControlGraphSupportProof InternalControlGraphChoiceProof InternalPairingSupportProof
open InternalRecursionClosureLogicProof InternalPairingSumBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof InternalBetaTotalityProof

theorem actualOriginalPairingSumBound : InternalPairingSumBoundsTargets.ActualOriginalPairingSumBound := by
  intro body α p x y
  let g := pairGraph p x y
  let psi := weakBound (add x y) p
  have hl : Nonempty (Derivation body (ltF x y :: [g]) psi) := by
    let Gamma := ltF x y :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing p
      (add (OrdinaryArithmetic.mulTerm y y) x)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfLess x y hc)
    obtain ⟨hb⟩ := lessBranchSum (body := body) (Gamma := Gamma) x y
    exact ⟨orderRight (add x y) (congSuc (symm he)) hb⟩
  have hn : Nonempty (Derivation body ((ltF x y).not :: [g]) psi) := by
    let Gamma := (ltF x y).not :: [g]
    have hc : Nonempty (Derivation body Gamma (ltF x y).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp : Nonempty (Derivation body Gamma g) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨he⟩ := valueUnique InternalPairing.pairing p
      (add (add (OrdinaryArithmetic.mulTerm x x) x) y)
      (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfNotLess x y hc)
    obtain ⟨hb⟩ := nonLessBranchSum (body := body) (Gamma := Gamma) x y
    exact ⟨orderRight (add x y) (congSuc (symm he)) hb⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination (excludedMiddle (ltF x y))
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hn))⟩

theorem actualOriginalApplicationPayloadChildFuelBound :
    InternalPairingSumBoundsTargets.ActualOriginalApplicationPayloadChildFuelBound := by
  intro body α payload middle children d fp ap
  let premise := applicationPayloadWitnesses payload middle children d fp ap
  let Gamma := [premise]
  have hp : Derivation body Gamma premise := Derivation.hypothesis List.mem_cons_self
  have houter : Nonempty (Derivation body Gamma (weakBound (add (suc (suc z)) middle) payload)) :=
    closedApply (actualOriginalPairingSumBound body α payload (suc (suc z)) middle)
      ⟨Derivation.conjunctionLeft hp⟩
  have hmiddle : Nonempty (Derivation body Gamma (weakBound (add d children) middle)) :=
    closedApply (actualOriginalPairingSumBound body α middle d children)
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hp)⟩
  have hchildren : Nonempty (Derivation body Gamma (weakBound (add fp ap) children)) :=
    closedApply (actualOriginalPairingSumBound body α children fp ap)
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hp)⟩
  have hm := weakTrans children (add d children) middle (rightWeakAdd d children) hmiddle
  have hc := weakTrans (add fp ap) children middle hchildren hm
  have ht := addWeakLeft (suc (suc z)) (add fp ap) middle hc
  obtain ⟨h⟩ := weakTrans (add (suc (suc z)) (add fp ap))
    (add (suc (suc z)) middle) payload ht houter
  exact ⟨Derivation.implicationIntroduction
    (orderLeft (suc payload) (symm (childSumExpansion fp ap)) h)⟩

theorem actualOriginalApplicationParentFuelBound :
    InternalPairingSumBoundsTargets.ActualOriginalApplicationParentFuelBound := by
  intro body α payload middle children d fp ap
  let premise := applicationPayloadWitnesses payload middle children d fp ap
  have h : Nonempty (Derivation body [premise] (weakBound (childFuelSum fp ap) payload)) :=
    closedApply (actualOriginalApplicationPayloadChildFuelBound body α payload middle children d fp ap)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := successorWeak (childFuelSum fp ap) payload h
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
