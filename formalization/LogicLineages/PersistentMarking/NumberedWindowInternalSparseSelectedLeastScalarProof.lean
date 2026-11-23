module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressScalarFromFixedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastScalarProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseRoundWindowChecks (exact_SelectedWindowFromRetained)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseAddressScalarFromFixedProof (exact_OpenAddressScalarFromOutputFixed)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The original actual selected minimum inherits W(k) from a genuine
seed window on the same least program; no selected window is assumed. -/
theorem exact_OpenSelectedWindowFromSeed (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed k : OTerm α)
    (seedW : Nonempty (Derivation B Γ (windowAt W ctx ty seed)))
    (pick : Nonempty (Derivation B Γ (leastGraph C X W s ctx ty seed k))) :
    Nonempty (Derivation B Γ (windowAt W ctx ty k)) := by
  obtain ⟨law⟩ := exact_SelectedWindowFromRetained exact_RetainedPredecessor C X W s B α Γ ctx ty seed k
  obtain ⟨w⟩ := seedW
  obtain ⟨p⟩ := pick
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction w p)⟩

/-- Same packed least report, same W and output address. The actual
result fixed-point report remains explicit for arbitrary chosen W/X. -/
theorem exact_OpenSelectedLeastAddressScalar (cv tv : Program 1) (C : Program 3)
    (X : Program 2) (W : Program 3) (s : Settings) (y ctx ty seed k : OTerm α)
    (output : Nonempty (Derivation B Γ (eqn y (addressTerm ctx ty k))))
    (contextOK : Nonempty (Derivation B Γ (unary cv (suc z) ctx)))
    (typeOK : Nonempty (Derivation B Γ (unary tv (suc z) ty)))
    (seedW : Nonempty (Derivation B Γ (windowAt W ctx ty seed)))
    (pick : Nonempty (Derivation B Γ (leastGraph C X W s ctx ty seed k)))
    (fixed : Nonempty (Derivation B Γ (leastGraph C X W s ctx ty k k))) :
    Nonempty (Derivation B Γ (unary (addressScalar cv tv W (packedLeastProgram C X W s)) (suc z) y)) :=
  exact_OpenAddressScalarFromOutputFixed cv tv W (packedLeastProgram C X W s) y ctx ty k
    output contextOK typeOK (exact_OpenSelectedWindowFromSeed C X W s ctx ty seed k seedW pick) fixed

#print axioms exact_OpenSelectedWindowFromSeed
#print axioms exact_OpenSelectedLeastAddressScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastScalarProof
