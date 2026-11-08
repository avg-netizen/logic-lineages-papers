module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalPairingSumBounds
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof InternalUnpairArithmeticProof
open InternalUnpairReverseBoundsArithmeticProof InternalRecursionClosureLogicProof
open InternalPairingSumBoundsProof

/-- Each original child payload is strictly below the original application
payload, by the checked joint child-fuel bound and internal addition laws. -/
theorem payloadStrictChildren {body : Positive (Fin 1)} {α : Type}
    {Gamma : List (Formula α)}
    (payload middle children d fp ap : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (applicationPayloadWitnesses payload middle children d fp ap))) :
    Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess fp payload ⊓ InternalLessThan.strictLess ap payload)) := by
  have hb : Nonempty (Derivation body Gamma (weakBound (childFuelSum fp ap) payload)) :=
    closedApply (actualOriginalApplicationPayloadChildFuelBound
      body α payload middle children d fp ap) h
  have hf : Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess fp (childFuelSum fp ap))) := by
    obtain ⟨hf⟩ := leftWeakAdd (body := body) (Gamma := Gamma) fp (suc ap)
    exact ⟨orderRight fp (symm (leftSuccessor fp (suc ap))) hf⟩
  have ha : Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess ap (childFuelSum fp ap))) := by
    obtain ⟨ha⟩ := rightWeakAdd (body := body) (Gamma := Gamma) (suc fp) ap
    exact ⟨orderRight ap (symm (addSucc (suc fp) ap)) ha⟩
  obtain ⟨hf⟩ := strictWeakTrans fp (childFuelSum fp ap) payload hf hb
  obtain ⟨ha⟩ := strictWeakTrans ap (childFuelSum fp ap) payload ha hb
  exact ⟨Derivation.conjunctionIntroduction hf ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningBoundsProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningBoundsProof
