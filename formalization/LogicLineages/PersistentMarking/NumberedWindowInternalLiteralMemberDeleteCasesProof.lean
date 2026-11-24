module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteAssembleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalSuccessorClosure)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique programRename)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof (listCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D compare)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalFunctionalRawRepackProof (exact_FunctionalRawRepackParser)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ singletonRename)
open NumberedWindowInternalLiteralSingletonStepProof (singletonCodeRename)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralJPermutationProof (exact_LiteralJPermutation)
open NumberedWindowInternalLiteralMemberDeleteAssembleProof (exact_LiteralMemberDeletionFromReports)

attribute [local irreducible] programGraph

structure ProjectionReports (i : Program 1) (B : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (raw key src one rest rebuilt : OTerm α) : Prop where
  parsed : D B Γ (unary parser (suc src) raw)
  singleton : D B Γ (unary parser (suc one) (singletonCode key))
  sourceTyped : D B Γ (unary (typedScratch i) (suc z) src)
  singletonTyped : D B Γ (unary (typedScratch i) (suc z) one)
  single : D B Γ (consGraph one key z)
  reinsert : D B Γ (consGraph rebuilt key rest)
  count : D B Γ (compare src rebuilt)

private theorem moveReports {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    {Δ : List (Formula β)} (i : Program 1) (raw key src one rest rebuilt : OTerm α)
    (h : ProjectionReports i B Γ raw key src one rest rebuilt)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    ProjectionReports i B Δ (raw.relabel j) (key.relabel j) (src.relabel j)
      (one.relabel j) (rest.relabel j) (rebuilt.relabel j) := by
  refine ⟨renameParser raw src h.parsed j Δ keep,?_,?_,?_,?_,?_,?_⟩
  · simpa only [singletonCodeRename] using renameParser (singletonCode key) one h.singleton j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto h.sourceTyped j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto h.singletonTyped j Δ keep
  · simpa only [consGraphRename,zRelabel] using renameInto h.single j Δ keep
  · simpa only [consGraphRename] using renameInto h.reinsert j Δ keep
  · simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) src rebuilt h.count j keep

private theorem rightTransport {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 2) (out left old new : OTerm α) (eq : D B Γ (eqn old new))
    (g : D B Γ (programGraph p out ![left,old])) :
    D B Γ (programGraph p out ![left,new]) := by
  unfold programGraph at g ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula p) out ![left,old] ![left,new] _ g
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · change D B Γ (equal left left)
    rw [equalEqn]
    exact ⟨refl left⟩
  · obtain rfl := Fin.eq_zero k
    change D B Γ (equal old new)
    rw [equalEqn]
    exact eq

private theorem emptyResidual (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (raw key src one rest rebuilt : OTerm α)
    (reports : ProjectionReports i (sourceBody (literalData i r) c) Γ raw key src one rest rebuilt)
    (JA : D (sourceBody (literalData i r) c) Γ (membership true raw))
    (empty : D (sourceBody (literalData i r) c) Γ (eqn rest z)) :
    D (sourceBody (literalData i r) c) Γ (singletonJ key) := by
  have code := rightTransport consCode rebuilt key rest z empty reports.reinsert
  have same := valueUnique consCode rebuilt one ![key,z] code reports.single
  have count := rightTransport permutation (suc z) src rebuilt one same reports.count
  exact exact_LiteralJPermutation i r c α Γ raw (singletonCode key) src one
    JA reports.parsed reports.singleton count

private theorem nonemptyResidual (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (raw key src one rest rebuilt dh dt : OTerm α)
    (reports : ProjectionReports i (sourceBody (literalData i r) c) Γ raw key src one rest rebuilt)
    (JA : D (sourceBody (literalData i r) c) Γ (membership true raw))
    (nonempty : D (sourceBody (literalData i r) c) Γ (consGraph rest dh dt)) :
    D (sourceBody (literalData i r) c) Γ (singletonJ key) := by
  let S := literalData i r
  let B := sourceBody S c
  apply programCases repack ![rest] _
  intro β j Δ removed keep result
  rw [singletonRename]
  have lifted := moveReports i raw key src one rest rebuilt reports j keep
  have typed := renameInto nonempty j Δ keep
  rw [consGraphRename] at typed
  have h := renameInto JA j Δ keep
  rw [membershipRename] at h
  rw [inputsRename] at result
  have good := exact_FunctionalRawRepackParser removed (rest.relabel j) result
  have step := exact_LiteralMemberDeletionFromReports i r c β Δ (raw.relabel j) (key.relabel j) removed
    (src.relabel j) (one.relabel j) (rest.relabel j) (rebuilt.relabel j) (dh.relabel j) (dt.relabel j)
    lifted.parsed lifted.singleton good lifted.sourceTyped lifted.singletonTyped lifted.single
    lifted.reinsert typed lifted.count
  exact actualOriginalSuccessorClosure S true c β Δ (raw.relabel j) (singletonCode (key.relabel j)) h step

/-- An empty residual is handled by the actual J permutation theorem.
A nonempty residual is repacked, removed with the exact strict
certificate, and justified by the actual J successor rule. -/
theorem exact_LiteralMemberProjectionAfterErase (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (raw key src one rest rebuilt : OTerm α)
    (reports : ProjectionReports i (sourceBody (literalData i r) c) Γ raw key src one rest rebuilt)
    (JA : D (sourceBody (literalData i r) c) Γ (membership true raw)) :
    D (sourceBody (literalData i r) c) Γ (singletonJ key) := by
  let S := literalData i r
  let B := sourceBody S c
  apply listCases rest (singletonJ key)
  · let Δ := eqn rest z :: Γ
    have lift {f : Formula α} (h : D B Γ f) : D B Δ f :=
      h.map (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp))
    have lifted : ProjectionReports i B Δ raw key src one rest rebuilt :=
      ⟨lift reports.parsed,lift reports.singleton,lift reports.sourceTyped,lift reports.singletonTyped,
        lift reports.single,lift reports.reinsert,lift reports.count⟩
    exact emptyResidual i r c raw key src one rest rebuilt lifted
      (lift JA) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro β j Δ dh dt keep cons
    rw [singletonRename]
    have lifted := moveReports i raw key src one rest rebuilt reports j keep
    have h := renameInto JA j Δ keep
    rw [membershipRename] at h
    exact nonemptyResidual i r c (raw.relabel j) (key.relabel j) (src.relabel j)
      (one.relabel j) (rest.relabel j) (rebuilt.relabel j) dh dt lifted h cons

#print axioms exact_LiteralMemberProjectionAfterErase
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteCasesProof
