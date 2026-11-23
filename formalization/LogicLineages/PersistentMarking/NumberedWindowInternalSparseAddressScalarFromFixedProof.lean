module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressScalarFromFixedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseAppliedEndpointReportProof (fromAddressEquation)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem readFields (q ctx ty k : OTerm α) (h : Derivation B Γ (addressReport q ctx ty k)) :
    ∀ j : Fin 3, Nonempty (Derivation B Γ (unary
      ((![rawContext,rawResult,rawLeast] : Fin 3 → Program 1) j)
      ((![ctx,ty,k] : Fin 3 → OTerm α) j) q)) := by
  have r := Derivation.conjunctionRight h
  intro j
  exact Fin.cases ⟨Derivation.conjunctionLeft r⟩
    (Fin.cases ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r)⟩
      (Fin.cases ⟨Derivation.conjunctionRight (Derivation.conjunctionRight r)⟩
        (fun n => Fin.elim0 n))) j

/-- Actual scalar acceptance at an already selected original address,
from the actual guards at its own displayed coordinates. The least
fixed point is at the selected term k, not a query at the earlier seed. -/
theorem exact_OpenAddressScalarFromHeldFixed (cv tv : Program 1) (W least : Program 3)
    (y ctx ty k : OTerm α)
    (address : Nonempty (Derivation B Γ (addressReport y ctx ty k)))
    (contextOK : Nonempty (Derivation B Γ (unary cv (suc z) ctx)))
    (typeOK : Nonempty (Derivation B Γ (unary tv (suc z) ty)))
    (window : Nonempty (Derivation B Γ (windowAt W ctx ty k)))
    (fixed : Nonempty (Derivation B Γ (programGraph least (suc k) ![ctx,ty,k]))) :
    Nonempty (Derivation B Γ (unary (addressScalar cv tv W least) (suc z) y)) := by
  obtain ⟨d⟩ := address
  obtain ⟨w⟩ := window
  obtain ⟨kfix⟩ := fixed
  obtain ⟨law⟩ := openTest W least B α Γ ctx ty k
  let checked := Derivation.implicationElimination (Derivation.conjunctionRight law)
    (Derivation.conjunctionIntroduction w kfix)
  have read := readFields y ctx ty k d
  have c := makeUnary cv rawContext (suc z) y ctx contextOK (read 0)
  have t := makeUnary tv rawResult (suc z) y ty typeOK (read 1)
  have shell := conjunctionAccept addressGood (conjunction (applyUnary cv rawContext) (applyUnary tv rawResult))
    ![y] ⟨Derivation.conjunctionLeft d⟩
    (conjunctionAccept (applyUnary cv rawContext) (applyUnary tv rawResult) ![y] c t)
  have coordinates := compositionValue (canonicalCoordinates W least) ![rawContext,rawResult,rawLeast]
    (suc z) ![y] ![ctx,ty,k] ⟨checked⟩ read
  exact conjunctionAccept (shapeChecks cv tv) (coordinateCall W least) ![y] shell coordinates

/-- The real output address equality is enough to obtain the unchanged
original selectors; no independent address packet is required. -/
theorem exact_OpenAddressScalarFromOutputFixed (cv tv : Program 1) (W least : Program 3)
    (y ctx ty k : OTerm α)
    (output : Nonempty (Derivation B Γ (eqn y (addressTerm ctx ty k))))
    (contextOK : Nonempty (Derivation B Γ (unary cv (suc z) ctx)))
    (typeOK : Nonempty (Derivation B Γ (unary tv (suc z) ty)))
    (window : Nonempty (Derivation B Γ (windowAt W ctx ty k)))
    (fixed : Nonempty (Derivation B Γ (programGraph least (suc k) ![ctx,ty,k]))) :
    Nonempty (Derivation B Γ (unary (addressScalar cv tv W least) (suc z) y)) :=
  exact_OpenAddressScalarFromHeldFixed cv tv W least y ctx ty k
    (fromAddressEquation y ctx ty k output) contextOK typeOK window fixed

#print axioms exact_OpenAddressScalarFromHeldFixed
#print axioms exact_OpenAddressScalarFromOutputFixed
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressScalarFromFixedProof
