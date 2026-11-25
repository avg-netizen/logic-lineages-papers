module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalCarrierInstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastFixedPointProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentChildProof
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
open NumberedWindowInternalLiteralSelectedChildWindowProof (exact_OpenSelectedWindowChildHopAtLeast)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralLeastFixedPointProof (exact_LiteralLeastFixedPointFromEdge)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- In the installed canonical carrier body, two computed child leasts
are enough to lift the raw child without an extra scalar premise:
generic admitted-selection and finite-round self-least discharge it.
The single exchange-edge preservation law stays explicit and applies
to the very same window, exchange and least AST. -/
theorem exact_OpenEdgeCoherentChildHopAtLeast (cv tv : Program 1) (C : Program 3) (X : Program 2)
    (W : Program 3) (s : Settings) (R : Program 5) (c : Nat) (ctx ty q w r a b : OTerm α)
    (paid : SameLeastOnEdge C X W s) :
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
    D B Γ (direct data (hop cv tv raw L) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  intro L i raw data B gc gt held left right valid
  exact exact_OpenSelectedWindowChildHopAtLeast cv tv C X W s R c ctx ty q w r a b gc gt held left right valid
    (exact_LiteralLeastFixedPointFromEdge C X W s paid ctx ty r b right)

#print axioms exact_OpenEdgeCoherentChildHopAtLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentChildProof
