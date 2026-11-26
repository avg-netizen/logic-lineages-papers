module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedChildWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenCanonicalChildHopAtLeast)
open NumberedWindowInternalSparseRoundWindowChecks (exact_SelectedWindowFromRetained)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Selection from the exact original pool preserves admission.
No guard at the output code, decoded pool, or caller-supplied
formula for the finite round invariant is assumed. -/
theorem exact_OpenLiteralSelectedWindow (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty q k : OTerm α) (valid : D B Γ (windowAt W ctx ty q))
    (least : D B Γ (leastGraph C X W s ctx ty q k)) :
    D B Γ (windowAt W ctx ty k) := by
  obtain ⟨rule⟩ := exact_SelectedWindowFromRetained exact_RetainedPredecessor C X W s B α Γ ctx ty q k
  obtain ⟨g⟩ := valid
  obtain ⟨m⟩ := least
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction g m)⟩

/-- A child already admitted in the selected window supplies the
window part of canonicality automatically. At the two computed
least values, only the actual least fixed-point report is additional
to the original validators and raw child's admitted endpoints. -/
theorem exact_OpenSelectedWindowChildHopAtLeast (cv tv : Program 1) (C : Program 3) (X : Program 2)
    (W : Program 3) (s : Settings) (R : Program 5) (c : Nat) (ctx ty q w r a b : OTerm α) :
    let L := packedLeastProgram C X W s
    let i := addressScalar cv tv W L
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r]) →
    D B Γ (leastGraph C X W s ctx ty q a) →
    D B Γ (leastGraph C X W s ctx ty r b) →
    D B Γ (windowAt W ctx ty r) →
    D B Γ (leastGraph C X W s ctx ty b b) →
    D B Γ (direct data (hop cv tv raw L) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  intro L i raw data B gc gt held left right valid self
  exact exact_OpenCanonicalChildHopAtLeast cv tv W L R c ctx ty q w r a b gc gt held left right
    (exact_OpenLiteralSelectedWindow C X W s ctx ty r b valid right) self

#print axioms exact_OpenLiteralSelectedWindow
#print axioms exact_OpenSelectedWindowChildHopAtLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedChildWindowProof
