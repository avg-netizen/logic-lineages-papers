module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPushedForwardImageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAdvanceScalarProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralPushedForwardImageProof (exact_OpenPlainFiniteScalarAtLeast)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
attribute [local irreducible] programGraph

/-- The head of an actual successful typed advance gives a finite
canonical target. Its real raw target window and unwrapped least,
not merely the option state, pay the scalar check. -/
theorem exact_OpenPlainTypedAdvanceScalar (cv tv : Program 1) (C W : Program 3) (X : Program 2)
    (s : Settings) (root other : Program 3) (V : Program 1) (paid : SameLeastOnEdge C X W s)
    (finite : List Nat) (ctx ty source cert target : OTerm α) :
    let L := packedLeastProgram C X W s
    let raw := typedRaw5 root other W V
    let i := finiteScalar (addressScalar cv tv W L) finite
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership finite ty) →
    D B Γ (selectedGraph raw L (suc target) ctx ty (suc source) cert) →
    D B Γ (unary i (suc z) (literalAddress ctx ty target)) := by
  intro L raw i gc gt finiteTy accepted
  obtain ⟨law⟩ := exact_OpenSuccessfulAdvanceCalls B raw L α ctx ty source cert target
  obtain ⟨report⟩ := accepted
  have obtained := Derivation.implicationElimination (Derivation.conjunctionLeft (weakenClosed law Γ)) report
  let goal := unary i (suc z) (addressTerm ctx ty target)
  change D B Γ goal
  apply reportCases raw L ctx ty source cert target goal ⟨obtained⟩
  intro β j Δ q w r keep row
  change D B Δ ((unary i (suc z) (addressTerm ctx ty target)).relabel j)
  rw [unaryRename,sucRelabel,zRelabel,renameAddress]
  have gc' := renameInto gc j Δ keep
  have gt' := renameInto gt j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at gc' gt'
  have finite' := renameInto finiteTy j Δ keep
  simp only [literalMembership,graphRename,numeralRename] at finite'
  obtain ⟨row⟩ := row
  let calls := Derivation.conjunctionRight row
  let val := Derivation.conjunctionRight calls
  let ctx' := ctx.relabel j
  let ty' := ty.relabel j
  obtain ⟨rule⟩ := exact_OpenTypedRaw5 B root other W V β Δ ctx' ty' q w r
  have gates := Derivation.implicationElimination (Derivation.conjunctionLeft rule)
    (Derivation.conjunctionLeft calls)
  exact exact_OpenPlainFiniteScalarAtLeast cv tv C W X s paid finite ctx' ty' r (target.relabel j)
    gc' gt' finite' ⟨Derivation.conjunctionRight (Derivation.conjunctionRight gates)⟩
    ⟨Derivation.conjunctionRight val⟩

#print axioms exact_OpenPlainTypedAdvanceScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAdvanceScalarProof
