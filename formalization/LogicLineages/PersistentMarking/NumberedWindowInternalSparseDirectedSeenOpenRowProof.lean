module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open GorbowVerifierNormalization (normalize)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem compareHead (w prior ctx ty v : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph headEq (suc z) (rowTape w prior ctx ty v)))) :
    Nonempty (Derivation body Γ (eqn w v)) := by
  let xs := rowTape w prior ctx ty v
  apply equalityOfAcceptance w v
  apply compositionRecover equalityTest (![.projection 0,.projection 4] : Fin 2 → Program 5)
    (suc z) xs (![w,v] : Fin 2 → OTerm α) accepted
  intro i
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 4 xs) (fun noIndex => Fin.elim0 noIndex)) i

private theorem actualEdge (E : Program 4) (w prior ctx ty v : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (edgeCall E) (suc z)
      (rowTape w prior ctx ty v)))) :
    Nonempty (Derivation body Γ (acceptEdge E ctx ty w v)) := by
  let xs := rowTape w prior ctx ty v
  apply compositionRecover E (![.projection 2,.projection 3,.projection 0,.projection 4] : Fin 4 → Program 5)
    (suc z) xs (edgeTape ctx ty w v) accepted
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
    (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 4 xs)
      (fun noIndex => Fin.elim0 noIndex)))) i

private theorem keepTail (E : Program 4) (w prior ctx ty v : OTerm α)
    (unmatched : Nonempty (Derivation body Γ (programGraph headEq (suc z) (rowTape w prior ctx ty v)).not))
    (unlinked : Nonempty (Derivation body Γ (programGraph (edgeCall E) (suc z) (rowTape w prior ctx ty v)).not))
    (accepted : Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) (rowTape w prior ctx ty v)))) :
    Nonempty (Derivation body Γ (eqn prior (suc z))) := by
  let xs := rowTape w prior ctx ty v
  have q := zeroBranchElim (normalize headEq)
    (branch (normalize (edgeCall E)) (.projection 1) (constantOne 5)) (constantOne 5)
    (suc z) xs (normalizeReject headEq xs unmatched) accepted
  have r := zeroBranchElim (normalize (edgeCall E)) (.projection 1) (constantOne 5)
    (suc z) xs (normalizeReject (edgeCall E) xs unlinked) q
  obtain ⟨e⟩ := valueUnique (.projection (1 : Fin 5)) (suc z) prior xs r (projectionValue 1 xs)
  exact ⟨symm e⟩

/-- Only the accepting row is inverted. Its fallback is the genuine
recursive tail value, not an external list-rejection theorem. -/
theorem rowCases (E : Program 4) (w prior ctx ty v : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) (rowTape w prior ctx ty v)))) :
    Nonempty (Derivation body Γ (eqn w v ⊔ (acceptEdge E ctx ty w v ⊔ eqn prior (suc z)))) := by
  let A := programGraph headEq (suc z) (rowTape w prior ctx ty v)
  let B := programGraph (edgeCall E) (suc z) (rowTape w prior ctx ty v)
  obtain ⟨accepted⟩ := accepted
  apply formulaCases A _
  · obtain ⟨same⟩ := compareHead (body := body) (Γ := A :: Γ) w prior ctx ty v
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨orLeft same⟩
  · apply formulaCases B _
    · obtain ⟨edge⟩ := actualEdge (body := body) (Γ := B :: A.not :: Γ) E w prior ctx ty v
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact ⟨orRight (orLeft edge)⟩
    · obtain ⟨tailBit⟩ := keepTail (body := body) (Γ := B.not :: A.not :: Γ) E w prior ctx ty v
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp (addHyp accepted A.not) B.not⟩
      exact ⟨orRight (orRight tailBit)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenRowProof
