module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicHeaderInstalledProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationScalarProof
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
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralLeastOnFixedPointProof
  (WindowEndpoints exact_OpenLeastOnWindow exact_OpenLeastOnFixedPoint)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
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

open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (OpenDecorator)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Once the actual seed's formation and validators are supplied, the
guarded selected least gives the result's canonical scalar. Recover
the underlying physical least call, apply its checked fixed-point
and window transfers, and rebuild the two actual self-guards. -/
theorem exact_OpenEnrichedApplicationScalar (cv tv : Program 1)
    (C W : Program 3) (E : Program 4) (s : Settings)
    (decorate : Program 3 → Program 3) (bridge : OpenDecorator decorate)
    (ends : WindowEndpoints W E) (paid : Preserves E (packedLeastOn C E s)) (ctx ty seed k y : OTerm α) :
    let L₀ := decorate (packedLeastOn C E s)
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
  have raw : D B Γ (leastOnGraph C E s ctx ty seed k) :=
    bridge.erase (packedLeastOn C E s) B α Γ ctx ty seed k ⟨Derivation.conjunctionLeft head⟩
  have win := exact_OpenLeastOnWindow C E s W ends ctx ty seed k raw formed
  have minimum := exact_OpenLeastOnFixedPoint C E s paid ctx ty seed k raw
  have fixedReport := exact_OpenLiteralGuardedSelfLeast L₀ ctx ty k
    (bridge.self (packedLeastOn C E s) B α Γ ctx ty k minimum)
  have scalar := exact_OpenLiteralScalarFromSelfLeast cv tv W L ctx ty k gc gt win fixedReport
  obtain ⟨eq⟩ := reported
  exact headTransport i (suc z) (addressTerm ctx ty k) y ![] ⟨symm eq⟩ scalar

#print axioms exact_OpenEnrichedApplicationScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationScalarProof
