module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseSuccessCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberProjectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCarrierExtraction)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D compare)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectTypedScratchIntroProof (exact_TypedScratchNil exact_IntroTypedScratchCons)
open NumberedWindowInternalDirectTypedScratchMemberProof (exact_TypedScratchMember)
open NumberedWindowInternalLiteralScratchEraseSuccessCasesProof (successCases)
open NumberedWindowInternalOriginalRawConsUnionReportThinProof (actualRawConsParser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ singletonRename)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalLiteralMemberDeleteCasesProof
  (ProjectionReports exact_LiteralMemberProjectionAfterErase)

attribute [local irreducible] programGraph

private theorem withErase (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw src key : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (membership true raw) → D B Γ (unary parser (suc src) raw) →
    D B Γ (unary (typedScratch i) (suc z) src) → D B Γ (memberGraph src key) →
    D B Γ (singletonJ key) := by
  dsimp only
  intro JA pa typed member
  let S := literalData i r
  let B := sourceBody S c
  obtain ⟨rule⟩ := exact_TypedScratchMember i B α Γ src key
  obtain ⟨st⟩ := typed
  obtain ⟨mem⟩ := member
  have keyTyped : D B Γ (unary i (suc z) key) :=
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction st mem)⟩
  apply successCases src key (singletonJ key) ⟨mem⟩
  intro β j Δ rest rebuilt retain reinsert count
  rw [singletonRename]
  let raw' := raw.relabel j
  let src' := src.relabel j
  let key' := key.relabel j
  have ja := renameInto JA j Δ retain
  rw [membershipRename] at ja
  have typedSrc := renameInto ⟨st⟩ j Δ retain
  have typedKey := renameInto keyTyped j Δ retain
  simp only [unaryRename,sucRelabel,zRelabel] at typedSrc typedKey
  have source := renameParser raw src pa j Δ retain
  apply programCases consCode ![key',z] _
  intro γ k Ω one keep selected
  rw [singletonRename]
  rw [binaryInputsRename,zRelabel] at selected
  have keyNow := renameInto typedKey k Ω keep
  have srcNow := renameInto typedSrc k Ω keep
  simp only [unaryRename,sucRelabel,zRelabel] at keyNow srcNow
  have erased := renameInto reinsert k Ω keep
  rw [consGraphRename] at erased
  have comp := renamePair permutation (suc z) src' rebuilt count k keep
  simp only [sucRelabel,zRelabel] at comp
  have single := actualRawConsParser (key'.relabel k) z z one exact_OriginalSparseParserNil selected
  have tyOne := exact_IntroTypedScratchCons i B γ Ω one (key'.relabel k) z selected keyNow
    (exact_TypedScratchNil i B γ Ω)
  have proofs : ProjectionReports i B Ω (raw'.relabel k) (key'.relabel k)
      (src'.relabel k) one (rest.relabel k) (rebuilt.relabel k) :=
    ⟨renameParser raw' src' source k Ω keep,single,srcNow,tyOne,selected,erased,comp⟩
  have ja' := renameInto ja k Ω keep
  rw [membershipRename] at ja'
  exact exact_LiteralMemberProjectionAfterErase i r c (raw'.relabel k) (key'.relabel k)
    (src'.relabel k) one (rest.relabel k) (rebuilt.relabel k) proofs ja'

/-- Project any held actual occurrence from a raw J member to its
exact singleton J. This handles an empty remainder by permutation,
not by inventing a strict same-length edge. -/
theorem exact_LiteralJMemberSingleton (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw src key : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (membership true raw) → D B Γ (unary parser (suc src) raw) →
    D B Γ (memberGraph src key) → D B Γ (singletonJ key) := by
  dsimp only
  intro JA given member
  let S := literalData i r
  let B := sourceBody S c
  have carrier := actualOriginalCarrierExtraction S true c α Γ raw JA
  have parsed := (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ raw).1 carrier
  apply exact_OpenJRaw i B α Γ raw (singletonJ key) parsed
  intro β j Δ actual keep facts
  rw [singletonRename]
  have same := renameParser raw src given j Δ keep
  obtain ⟨ee⟩ := valueUnique parser (suc (src.relabel j)) (suc actual) ![raw.relabel j] same facts.parsed
  have belongs := renameInto member j Δ keep
  rw [graphRename] at belongs
  have aligned : D B Δ (memberGraph actual (key.relabel j)) :=
    headTransport scratchMember (suc z) (src.relabel j) actual
      (Fin.cons (key.relabel j) Fin.elim0) ⟨cancelSuc ee⟩ belongs
  have jRaw := renameInto JA j Δ keep
  rw [membershipRename] at jRaw
  exact withErase i r c β Δ (raw.relabel j) actual (key.relabel j) jRaw facts.parsed facts.typed aligned

#print axioms exact_LiteralJMemberSingleton
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberProjectionProof
