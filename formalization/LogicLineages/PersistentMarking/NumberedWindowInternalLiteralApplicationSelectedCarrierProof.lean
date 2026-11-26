module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicHeaderInstalledProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedChildWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastFixedPointProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationSelectedCarrierProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralLeastFixedPointProof (exact_LiteralLeastFixedPointFromEdge)
open NumberedWindowInternalLiteralSelectedChildWindowProof (exact_OpenLiteralSelectedWindow)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenLiteralScalarFromSelfLeast)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralGuardedSelfLeastProof (exact_OpenLiteralGuardedSelfLeast)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Once the actual seed's formation and validators are supplied, the
guarded selected least gives the result's canonical scalar. Recover
the underlying physical least call, apply its checked fixed-point
and window transfers, and rebuild the two actual self-guards. -/
theorem exact_OpenLiteralApplicationScalarAtSelected (cv tv : Program 1)
    (C W : Program 3) (X : Program 2) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed k y : OTerm α) :
    let L₀ := packedLeastProgram C X W s
    let L := guardedLeast (headerLeast L₀)
    let i := addressScalar cv tv W L
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (windowAt W ctx ty seed) →
    D B Γ (programGraph L (suc k) ![ctx,ty,seed]) →
    D B Γ (eqn y (addressTerm ctx ty k)) →
    D B Γ (unary i (suc z) y) := by
  intro L₀ L i gc gt formed selected reported
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast L₀) ctx ty seed k selected
  obtain ⟨head⟩ := exact_OpenLiteralHeaderLeastReport L₀ ctx ty seed k
    ⟨Derivation.conjunctionLeft atom⟩
  have raw : D B Γ (leastGraph C X W s ctx ty seed k) := ⟨Derivation.conjunctionLeft head⟩
  have win := exact_OpenLiteralSelectedWindow C X W s ctx ty seed k formed raw
  have minimum := exact_LiteralLeastFixedPointFromEdge C X W s paid ctx ty seed k raw
  have fixedReport := exact_OpenLiteralGuardedSelfLeast L₀ ctx ty k minimum
  have scalar := exact_OpenLiteralScalarFromSelfLeast cv tv W L ctx ty k gc gt win fixedReport
  obtain ⟨eq⟩ := reported
  exact headTransport i (suc z) (addressTerm ctx ty k) y ![] ⟨symm eq⟩ scalar

/-- Recover the actual output carrier in the exact installed ordinary
body, subject to the explicit seed-formation and context/type reports.
No new proof principle is built into the application rule. -/
theorem exact_OpenLiteralApplicationCarrierAtSelected (cv tv : Program 1)
    (C W : Program 3) (X : Program 2) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (raw : Program 5) (c : Nat)
    (ctx ty seed k y : OTerm α) :
    let L := guardedLeast (headerLeast (packedLeastProgram C X W s))
    let i := addressScalar cv tv W L
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (windowAt W ctx ty seed) →
    D B Γ (programGraph L (suc k) ![ctx,ty,seed]) →
    D B Γ (eqn y (addressTerm ctx ty k)) →
    D B Γ (carrier data false c y) := by
  intro L i R data B gc gt formed selected eq
  have h := exact_OpenLiteralApplicationScalarAtSelected cv tv C W X s paid
    ctx ty seed k y gc gt formed selected eq
  let k := addressPositive cv tv R L
  exact (exact_DomainRules i (jRaw i) k (dCore i k permutation) false c B α Γ y).2 h

#print axioms exact_OpenLiteralApplicationScalarAtSelected
#print axioms exact_OpenLiteralApplicationCarrierAtSelected
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationSelectedCarrierProof
