module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedApplicationInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCarrierChildHopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedCanonicalChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_MakeLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof
  (WindowEndpoints exact_OpenLeastOnWindow exact_OpenLeastOnFixedPoint)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers exact_OpenChildGuardLeastInstalled)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
  (fullAuxiliaryDecorator exact_FullAuxiliaryDecoratorOpen exact_OpenFullFilteredNonAuxLeast)
open NumberedWindowInternalLiteralGuardedSelfLeastProof (exact_OpenLiteralGuardedSelfLeast)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenLiteralScalarFromSelfLeast)
open NumberedWindowInternalLiteralCarrierChildHopProof (exact_OpenCarrierChildHopAtLeast)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Successful enriched least at a formed child gives the child's
finite scalar at its exact advertised canonical address. Self-reports
for the full decorator are built reflexively; no class transfer over
a different raw representative is used in this scalar proof. -/
theorem exact_OpenEnrichedCanonicalChild (cv tv : Program 1) (C W : Program 3) (E : Program 4) (s : Settings)
    (finite : List Nat) (ctx ty q k : OTerm α)
    (ends : WindowEndpoints W E) (stable : Preserves E (packedLeastOn C E s))
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (inTypes : D B Γ (literalMembership finite ty))
    (formed : D B Γ (windowAt W ctx ty q))
    (least : D B Γ (leastOnGraph C E s ctx ty q k)) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C E s)))
    D B Γ (unary (finiteScalar (addressScalar cv tv W L) finite) (suc z) (literalAddress ctx ty k)) := by
  let L₀ := fullAuxiliaryDecorator (packedLeastOn C E s)
  let L := guardedLeast (headerLeast L₀)
  have win := exact_OpenLeastOnWindow C E s W ends ctx ty q k least formed
  have self := exact_OpenLeastOnFixedPoint C E s stable ctx ty q k least
  have full := exact_OpenLiteralGuardedSelfLeast L₀ ctx ty k
    (exact_FullAuxiliaryDecoratorOpen.self (packedLeastOn C E s) B α Γ ctx ty k self)
  have addr := exact_OpenLiteralScalarFromSelfLeast cv tv W L ctx ty k gc gt win full
  obtain ⟨_,_,typeReport,_⟩ := NumberedWindowInternalAtomicRefinementObjectSelectorsProof.literalAddress
    (body := B) (Γ := Γ) ctx ty k
  exact exact_MakeLiteralFiniteScalar (addressScalar cv tv W L) finite (literalAddress ctx ty k) ty
    typeReport addr inTypes

theorem exact_OpenEnrichedNonAuxSelected (C : Program 3) (baseE : Program 4) (s : Settings)
    (ctx ty q k : OTerm α) :
    let E := withObservers baseE childGuardObservers
    let L₀ := packedLeastOn C E s
    D B Γ (leastOnGraph C E s ctx ty q k) → D B Γ (unary termShape z q) →
    D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))) (suc k) ![ctx,ty,q]) := by
  intro E L₀ raw shape
  exact exact_OpenFullFilteredNonAuxLeast L₀ ctx ty q k shape
    (exact_OpenChildGuardLeastInstalled C baseE s ctx ty q k raw)

/-- A genuine raw child whose selected destination is not an auxiliary
now yields the required actual direct certificate between finite
canonical addresses, with the full least AST kept in the hop. -/
theorem exact_OpenEnrichedCanonicalChildHopNonAux (cv tv : Program 1) (C W : Program 3)
    (baseE : Program 4) (s : Settings) (raw : Program 5) (finite : List Nat) (c : Nat)
    (ctx ty q w r a b : OTerm α) :
    let E := withObservers baseE childGuardObservers
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C E s)))
    let i := finiteScalar (addressScalar cv tv W L) finite
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    WindowEndpoints W E → Preserves E (packedLeastOn C E s) →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership finite ty) → D B Γ (windowAt W ctx ty r) →
    D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r]) →
    D B Γ (programGraph L (suc a) ![ctx,ty,q]) →
    D B Γ (leastOnGraph C E s ctx ty r b) → D B Γ (unary termShape z r) →
    D B Γ (direct data (hop cv tv R L) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  intro E L i R data B ends stable gc gt finiteType formed step left primitive noAux
  have right := exact_OpenEnrichedNonAuxSelected C baseE s ctx ty r b primitive noAux
  have scalar := exact_OpenEnrichedCanonicalChild cv tv C W E s finite ctx ty r b ends stable
    gc gt finiteType formed primitive
  exact exact_OpenCarrierChildHopAtLeast i cv tv raw L c ctx ty q w r a b gc gt step left right scalar

#print axioms exact_OpenEnrichedCanonicalChild
#print axioms exact_OpenEnrichedNonAuxSelected
#print axioms exact_OpenEnrichedCanonicalChildHopNonAux
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedCanonicalChildProof
