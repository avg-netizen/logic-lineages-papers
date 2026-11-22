module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenRowProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open GorbowVerifierNormalization (normalize)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue outputTransport)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenOpenRowProof (rowCases)
open NumberedWindowInternalSparseScanRetentionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
private abbrev inner (E : Program 4) := branch (normalize (edgeCall E)) (.projection 1) (constantOne 5)

private theorem matchHead (w prev ctx ty k : OTerm α) (same : Derivation body Γ (eqn w k)) :
    Nonempty (Derivation body Γ (programGraph headEq (suc z) (rowTape w prev ctx ty k))) := by
  let xs := rowTape w prev ctx ty k
  apply compositionValue equalityTest (![.projection 0,.projection 4] : Fin 2 → Program 5) (suc z) xs ![w,k]
    (equalityOfEqual w k ⟨same⟩)
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 4 xs) (fun z => Fin.elim0 z)) i

private theorem matchEdge (E : Program 4) (w prev ctx ty k : OTerm α)
    (edge : Derivation body Γ (acceptEdge E ctx ty w k)) :
    Nonempty (Derivation body Γ (programGraph (edgeCall E) (suc z) (rowTape w prev ctx ty k))) := by
  let xs := rowTape w prev ctx ty k
  apply compositionValue E (![.projection 2,.projection 3,.projection 0,.projection 4] : Fin 4 → Program 5)
    (suc z) xs (edgeTape ctx ty w k) ⟨edge⟩
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
    (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 4 xs) (fun z => Fin.elim0 z)))) i

private theorem headYes (E : Program 4) (xs : Fin 5 → OTerm α)
    (yes : Nonempty (Derivation body Γ (programGraph headEq (suc z) xs))) :
    Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) xs)) :=
  successorBranchIntro (normalize headEq) (inner E) (constantOne 5) (suc z) z xs
    (normalizeAccept headEq xs yes) (oneConstantValue xs)

private theorem fromInner (E : Program 4) (xs : Fin 5 → OTerm α)
    (inside : Nonempty (Derivation body Γ (programGraph (inner E) (suc z) xs))) :
    Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) xs)) := by
  let A := programGraph headEq (suc z) xs
  apply formulaCases A _
  · exact headYes E xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  · obtain ⟨d⟩ := inside
    exact zeroBranchIntro (normalize headEq) (inner E) (constantOne 5) (suc z) xs
      (normalizeReject headEq xs ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp d A.not⟩

private theorem edgeYes (E : Program 4) (xs : Fin 5 → OTerm α)
    (yes : Nonempty (Derivation body Γ (programGraph (edgeCall E) (suc z) xs))) :
    Nonempty (Derivation body Γ (programGraph (inner E) (suc z) xs)) :=
  successorBranchIntro (normalize (edgeCall E)) (.projection 1) (constantOne 5) (suc z) z xs
    (normalizeAccept _ xs yes) (oneConstantValue xs)

private theorem fromPrior (E : Program 4) (w prev ctx ty k : OTerm α)
    (same : Derivation body Γ (eqn prev (suc z))) :
    Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) (rowTape w prev ctx ty k))) := by
  let xs := rowTape w prev ctx ty k
  let B := programGraph (edgeCall E) (suc z) xs
  apply fromInner E xs
  apply formulaCases B _
  · exact edgeYes E xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have saved := outputTransport (body := body) (Gamma := B.not :: Γ) (.projection (1 : Fin 5)) prev
      (suc z) xs ⟨addHyp same B.not⟩ (projectionValue 1 xs)
    exact zeroBranchIntro (normalize (edgeCall E)) (.projection 1) (constantOne 5) (suc z) xs
      (normalizeReject (edgeCall E) xs ⟨Derivation.hypothesis List.mem_cons_self⟩) saved

theorem rowBranches : ExactScanRowBranches := by
  intro E body α Γ h prev ctx ty k
  let R := programGraph (scanStep E) (suc z) (rowTape h prev ctx ty k)
  let A := eqn h k
  let B := acceptEdge E ctx ty h k
  let D := eqn prev (suc z)
  let H := A ⊔ (B ⊔ D)
  obtain ⟨f⟩ := rowCases (body := body) (Γ := R :: Γ) E h prev ctx ty k ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hypotheses : Derivation body (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨a⟩ := headYes (body := body) (Γ := A :: H :: Γ) E (rowTape h prev ctx ty k)
    (matchHead h prev ctx ty k (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨b⟩ := fromInner (body := body) (Γ := B :: (B ⊔ D) :: H :: Γ) E (rowTape h prev ctx ty k)
    (edgeYes E _ (matchEdge E h prev ctx ty k (Derivation.hypothesis List.mem_cons_self)))
  obtain ⟨d⟩ := fromPrior (body := body) (Γ := D :: (B ⊔ D) :: H :: Γ) E h prev ctx ty k
    (Derivation.hypothesis List.mem_cons_self)
  have rest : Derivation body ((B ⊔ D) :: H :: Γ) R :=
    disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (Derivation.implicationIntroduction b) (Derivation.implicationIntroduction d)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction (disjunctionElimination hypotheses (Derivation.implicationIntroduction a)
      (Derivation.implicationIntroduction rest)))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionRowProof
