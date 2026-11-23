module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCertifiedSuccessorClosure)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountMembershipChecks (exact_OpenLiteralTargetMemberLaw)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralMemberReverse)
open NumberedWindowInternalDirectInstalledOriginChecks (exact_InstalledOriginalSuccessorOrigin)
open NumberedWindowInternalDirectInstalledOriginSyntaxProof (targetMember)
open NumberedWindowInternalScratchAppendOpenChecks (exact_OpenScratchAppendMembership)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph appears)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (scalarMembers scalarMembersRename)
open NumberedWindowInternalLiteralSparseJFoldSupportProof (applyScalarMembers)
open NumberedWindowInternalLiteralSingletonProgressSyntaxProof (oddCertificateRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralBaseStepScalarTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem memberFromSource (source ds actual kept removed combined key : OTerm α)
    (given : Nonempty (Derivation B Γ (unary parser (suc ds) source)))
    (reported : Nonempty (Derivation B Γ (unary parser (suc actual) source)))
    (app : Nonempty (Derivation B Γ (appendGraph combined kept removed)))
    (count : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![actual,combined])))
    (origin : Nonempty (Derivation B Γ (appears kept removed key))) :
    Nonempty (Derivation B Γ (memberGraph ds key)) := by
  have inCombined := exact_OpenScratchAppendMembership B α Γ kept removed combined key app origin
  have inActual := exact_LiteralMemberReverse B α Γ actual combined key count inCombined
  exact targetMember source actual ds key reported given inActual

theorem exact_OpenLiteralBaseStepScalarMember : ExactOpenLiteralBaseStepScalarMember := by
  intro i r c α Γ source target witness ds dt key
  dsimp only
  intro cert pS pT members occurs
  let S := literalData i r
  let B := sourceBody S c
  let goal := membership false key
  apply exact_InstalledOriginalSuccessorOrigin i (jRaw i) r permutation c α Γ
    source witness target dt key goal (exact_OpenLiteralTargetMemberLaw B) cert pT occurs
  · intro β j Δ _ _ _ s t k d a p sk tp keep held yes
    have sourceView := renameParser source ds pS j Δ keep
    have saved := renameInto members j Δ keep
    rw [scalarMembersRename] at saved
    obtain ⟨member⟩ := yes
    have old := memberFromSource (source.relabel j) (ds.relabel j) s k d sk (key.relabel j)
      sourceView held.sourceParsed held.sourceAppend held.sourceObserved ⟨orLeft member⟩
    simp only [goal,membershipRename]
    exact applyScalarMembers (ds.relabel j) (key.relabel j) saved old
  · intro β j Δ _ _ _ s t k d a p sk tp row dom proof keep held _ originalRow
    have sourceView := renameParser source ds pS j Δ keep
    have saved := renameInto members j Δ keep
    rw [scalarMembersRename] at saved
    obtain ⟨report⟩ := originalRow.original
    have details := Derivation.conjunctionRight report
    have own := memberFromSource (source.relabel j) (ds.relabel j) s k d sk dom
      sourceView held.sourceParsed held.sourceAppend held.sourceObserved
      ⟨orRight (Derivation.conjunctionLeft details)⟩
    have domI := applyScalarMembers (ds.relabel j) dom saved own
    have positive : Nonempty (Derivation B Δ (programGraph r (suc z) ![dom,proof,key.relabel j])) :=
      ⟨Derivation.conjunctionRight details⟩
    unfold programGraph at positive
    have scalarCert := (exact_CertificateRules i (jRaw i) r (dCore i r permutation)
      false c B β Δ dom (key.relabel j) proof).2 positive
    simp only [goal,membershipRename]
    exact actualOriginalCertifiedSuccessorClosure S false c β Δ dom (key.relabel j) proof domI scalarCert

/-- Original scalar accessibility of all genuine target entries is
preserved by the actual certified packed replacement; no external
choice of a removed dominator and no occurrence-set approximation. -/
theorem exact_OpenLiteralBaseStepScalarMembers : ExactOpenLiteralBaseStepScalarMembers := by
  intro i r c α Γ source target witness ds dt
  dsimp only
  intro cert pS pT members
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := memberGraph (dt.relabel j) key
  let Δ := H :: Γ.map weaken
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ :=
    fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have cert' := renameInto cert j Δ keep
  rw [oddCertificateRename] at cert'
  have members' := renameInto members j Δ keep
  rw [scalarMembersRename] at members'
  obtain ⟨point⟩ := exact_OpenLiteralBaseStepScalarMember i r c (α ⊕ Fin 1) Δ
    (source.relabel j) (target.relabel j) (witness.relabel j) (ds.relabel j) (dt.relabel j) key
    cert' (renameParser source ds pS j Δ keep) (renameParser target dt pT j Δ keep) members'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction point)⟩

#print axioms exact_OpenLiteralBaseStepScalarMember
#print axioms exact_OpenLiteralBaseStepScalarMembers

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarProof
