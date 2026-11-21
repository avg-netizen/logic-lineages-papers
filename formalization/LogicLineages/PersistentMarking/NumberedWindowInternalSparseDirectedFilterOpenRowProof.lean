module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open GorbowVerifierNormalization (normalize)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodec (consCode)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (scan scanGraph scanTape)
open NumberedWindowInternalSparseDirectedFilter

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem scanParts (h rest seen ctx ty : OTerm α) :
    ∀ i : Fin 4, Nonempty (Derivation body Γ (programGraph
      ((![.projection 2,.projection 3,.projection 4,.projection 0] : Fin 4 → Program 5) i)
      (scanTape seen ctx ty h i) (filterTape h rest seen ctx ty))) := by
  intro i
  let xs := filterTape h rest seen ctx ty
  exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 0 xs)
      (fun noIndex => Fin.elim0 noIndex)))) i

private theorem selectScan (E : Program 4) (h rest seen ctx ty : OTerm α)
    (ok : Nonempty (Derivation body Γ (scanGraph E seen ctx ty h))) :
    Nonempty (Derivation body Γ (programGraph (scanHead E) (suc z)
      (filterTape h rest seen ctx ty))) :=
  compositionValue (scan E) ![.projection 2,.projection 3,.projection 4,.projection 0]
    (suc z) (filterTape h rest seen ctx ty) (scanTape seen ctx ty h) ok
    (scanParts h rest seen ctx ty)

private theorem recoverScan (E : Program 4) (h rest seen ctx ty : OTerm α)
    (ok : Nonempty (Derivation body Γ (programGraph (scanHead E) (suc z)
      (filterTape h rest seen ctx ty)))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty h)) :=
  compositionRecover (scan E) ![.projection 2,.projection 3,.projection 4,.projection 0]
    (suc z) (filterTape h rest seen ctx ty) (scanTape seen ctx ty h) ok
    (scanParts h rest seen ctx ty)

private theorem retain (E : Program 4) (out h rest seen ctx ty : OTerm α)
    (ok : Nonempty (Derivation body Γ (programGraph (scanHead E) (suc z)
      (filterTape h rest seen ctx ty))))
    (run : Nonempty (Derivation body Γ (programGraph (filterStep E) out (filterTape h rest seen ctx ty)))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty h ⊓ cell out h rest)) := by
  let xs := filterTape h rest seen ctx ty
  have accepted := successorBranchElim (normalize (scanHead E)) (.projection 1) prependHead
    out z xs (normalizeAccept (scanHead E) xs ok) run
  have built : Nonempty (Derivation body Γ (cell out h rest)) := by
    apply compositionRecover consCode (![.projection 0,.projection 1] : Fin 2 → Program 5)
      out xs (![h,rest] : Fin 2 → OTerm α) accepted
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (fun noIndex => Fin.elim0 noIndex)) i
  obtain ⟨chosen⟩ := recoverScan E h rest seen ctx ty ok
  obtain ⟨built⟩ := built
  exact ⟨Derivation.conjunctionIntroduction chosen built⟩

private theorem skip (E : Program 4) (out h rest seen ctx ty : OTerm α)
    (failed : Nonempty (Derivation body Γ
      (programGraph (scanHead E) (suc z) (filterTape h rest seen ctx ty)).not))
    (run : Nonempty (Derivation body Γ (programGraph (filterStep E) out (filterTape h rest seen ctx ty)))) :
    Nonempty (Derivation body Γ ((scanGraph E seen ctx ty h).not ⊓ eqn out rest)) := by
  let xs := filterTape h rest seen ctx ty
  let Q := scanGraph E seen ctx ty h
  have rejected := zeroBranchElim (normalize (scanHead E)) (.projection 1) prependHead out xs
    (normalizeReject (scanHead E) xs failed) run
  obtain ⟨same⟩ := valueUnique (.projection (1 : Fin 5)) out rest xs rejected (projectionValue 1 xs)
  obtain ⟨notSelected⟩ := failed
  obtain ⟨selected⟩ := selectScan (body := body) (Γ := Q :: Γ) E h rest seen ctx ty
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have negative : Derivation body Γ (scanGraph E seen ctx ty h).not :=
    Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp notSelected Q) selected)
  exact ⟨Derivation.conjunctionIntroduction negative same⟩

/-- The object negative formula is only the other physical row branch.
No converse about witnesses or semantic scan rejection is needed. -/
theorem rowCases (E : Program 4) (out h rest seen ctx ty : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph (filterStep E) out (filterTape h rest seen ctx ty)))) :
    Nonempty (Derivation body Γ
      ((scanGraph E seen ctx ty h ⊓ cell out h rest) ⊔ ((scanGraph E seen ctx ty h).not ⊓ eqn out rest))) := by
  let A := programGraph (scanHead E) (suc z) (filterTape h rest seen ctx ty)
  obtain ⟨run⟩ := run
  obtain ⟨yes⟩ := retain (body := body) (Γ := A :: Γ) E out h rest seen ctx ty
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp run A⟩
  obtain ⟨no⟩ := skip (body := body) (Γ := A.not :: Γ) E out h rest seen ctx ty
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp run A.not⟩
  exact ⟨disjunctionElimination (excludedMiddle A)
    (Derivation.implicationIntroduction (orLeft yes))
    (Derivation.implicationIntroduction (orRight no))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenRowProof
