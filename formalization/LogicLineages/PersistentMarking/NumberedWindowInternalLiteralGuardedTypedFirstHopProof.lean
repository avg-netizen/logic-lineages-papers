module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAdvanceScalarProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedFirstHopCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedTypedFirstHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralPositiveEndpointGuardProof (positiveEndpointGuard)
open NumberedWindowInternalLiteralGuardedPositiveRowsProof (exact_OpenGuardedPositiveCertificateRows)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalOriginalFirstHopCoreProof (oneHopProgram)
open NumberedWindowInternalOriginalFirstHopTailProof (firstHopRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalNeutralFactsTargets (firstHop)
open NumberedWindowInternalLiteralTypedAdvanceScalarProof (exact_OpenPlainTypedAdvanceScalar)
open NumberedWindowInternalLiteralGuardedFirstHopCoreProof (exact_OpenGuardedFirstHopAtHead)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- A genuine positive certificate on the endpoint-guarded typed
tuple has the original one-cell head and a positive suffix on the
same guarded presentation. The intermediate scalar is derived
from the actual head advance, not supplied as a transport premise. -/
theorem exact_OpenGuardedTypedFirstHop (cv tv : Program 1) (C W : Program 3) (X : Program 2)
    (s : Settings) (root other : Program 3) (V : Program 1) (paid : SameLeastOnEdge C X W s)
    (finite : List Nat) (c : Nat) (x y : OTerm α) :
    let L := packedLeastProgram C X W s
    let raw := typedRaw5 root other W V
    let i := finiteScalar (addressScalar cv tv W L) finite
    let r := addressPositive cv tv raw L
    let data := literalData i (positiveEndpointGuard i r)
    let B := sourceBody data c
    D B Γ (edge data false c x y) → D B Γ (firstHop data (oneHopProgram r) c x y) := by
  intro L raw i r data B accepted
  let h := oneHopProgram r
  apply exact_OpenGuardedPositiveCertificateRows i cv tv raw L c x y (firstHop data h c x y) accepted
  intro β j Δ ctx ty src dst w keep left right scalarX scalarY gc gt fold
  rw [firstHopRename]
  obtain ⟨leftRead⟩ := left
  have field : D B Δ (unary rawResult ty (x.relabel j)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight leftRead))⟩
  obtain ⟨_,fin⟩ := exact_OpenLiteralFiniteScalar (addressScalar cv tv W L) finite (x.relabel j) ty field scalarX
  have opened := NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof.forward
    raw L ctx ty src w dst fold
  apply headCases raw L ctx ty src w dst (firstHop data h c (x.relabel j) (y.relabel j)) opened
  intro γ k Ω hd tl next stay fields
  rw [firstHopRename]
  have a := renameInto (⟨leftRead⟩ : D B Δ (addressReport (x.relabel j) ctx ty src)) k Ω stay
  have b := renameInto right k Ω stay
  rw [addressReportRename] at a b
  have cc := renameInto gc k Ω stay
  have tt := renameInto gt k Ω stay
  have last := renameInto scalarY k Ω stay
  simp only [unaryRename,sucRelabel,zRelabel] at cc tt last
  have member := renameInto fin k Ω stay
  simp only [literalMembership,graphRename,numeralRename] at member
  obtain ⟨row⟩ := fields
  let pieces := Derivation.conjunctionRight row
  have m := exact_OpenPlainTypedAdvanceScalar cv tv C W X s root other V paid finite
    (ctx.relabel k) (ty.relabel k) (src.relabel k) hd next cc tt member ⟨Derivation.conjunctionLeft pieces⟩
  exact exact_OpenGuardedFirstHopAtHead i cv tv raw L c ((x.relabel j).relabel k)
    ((y.relabel j).relabel k) (ctx.relabel k) (ty.relabel k) (src.relabel k) (dst.relabel k)
    hd tl next a b cc tt ⟨Derivation.conjunctionLeft pieces⟩ ⟨Derivation.conjunctionRight pieces⟩ m last

#print axioms exact_OpenGuardedTypedFirstHop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedTypedFirstHopProof
