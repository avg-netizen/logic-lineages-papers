module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAllQueries (eachAtPermutation)
open NumberedWindowInternalLiteralCountZeroChecks (exact_OpenLiteralZeroCountAbsent)
open NumberedWindowInternalLiteralCountAbsentChecks (exact_OpenLiteralAbsentCountZero)
open NumberedWindowInternalDirectTypedUnionScratchTargets (CountMembershipForward observer)
open NumberedWindowInternalDirectInstalledOriginTargets (TargetMemberLaw)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem impossible (left right key lc rc : OTerm α)
    (permit : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (hl : Nonempty (Derivation B Γ (counted left key lc)))
    (hr : Nonempty (Derivation B Γ (counted right key rc)))
    (member : Nonempty (Derivation B Γ (memberGraph left key)))
    (absent : Nonempty (Derivation B Γ (memberGraph right key).not)) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨equalCounts⟩ := eachAtPermutation left right key lc rc permit hl hr
  obtain ⟨absentLaw⟩ := exact_OpenLiteralAbsentCountZero B α Γ right key rc
  obtain ⟨m⟩ := member
  obtain ⟨n⟩ := absent
  obtain ⟨ar⟩ := hr
  have r0 := Derivation.implicationElimination absentLaw (Derivation.conjunctionIntroduction n ar)
  obtain ⟨l0⟩ := outputTransport entryCount lc z ![left,key] ⟨trans equalCounts r0⟩ hl
  obtain ⟨zeroLaw⟩ := exact_OpenLiteralZeroCountAbsent B α Γ left key
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination zeroLaw l0) m⟩

private theorem moveReport {β : Type} {Δ : List (Formula β)}
    (left right key : OTerm α)
    (p : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (m : Nonempty (Derivation B Γ (memberGraph left key)))
    (n : Nonempty (Derivation B Γ (memberGraph right key).not))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (programGraph permutation (suc z) ![left.relabel j,right.relabel j])) ∧
    Nonempty (Derivation B Δ (memberGraph (left.relabel j) (key.relabel j))) ∧
    Nonempty (Derivation B Δ (memberGraph (right.relabel j) (key.relabel j)).not) := by
  have p' : Nonempty (Derivation B Δ
      (programGraph permutation (suc z) ![left.relabel j,right.relabel j])) := by
    simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) left right p j keep
  have m' := renameInto m j Δ keep
  rw [graphRename] at m'
  have n' := renameInto n j Δ keep
  change Nonempty (Derivation B Δ ((memberGraph right key).relabel j).not) at n'
  rw [graphRename] at n'
  exact ⟨p',m',n'⟩

private theorem impossibleFromGraphs (left right key : OTerm α)
    (p : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (m : Nonempty (Derivation B Γ (memberGraph left key)))
    (n : Nonempty (Derivation B Γ (memberGraph right key).not)) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  apply programCases entryCount ![left,key] (⊥ : Formula α)
  intro β j Δ lc keep lcReport
  rw [binaryInputsRename] at lcReport
  obtain ⟨p',m',n'⟩ := moveReport left right key p m n j keep
  let L := left.relabel j
  let R := right.relabel j
  let K := key.relabel j
  change Nonempty (Derivation B Δ (⊥ : Formula β))
  apply programCases entryCount ![R,K] (⊥ : Formula β)
  intro γ k Ω rc keep' rcReport
  rw [binaryInputsRename] at rcReport
  obtain ⟨p'',m'',n''⟩ := moveReport L R K p' m' n' k keep'
  exact impossible (L.relabel k) (R.relabel k) (K.relabel k) (lc.relabel k) rc p''
    (renamePair entryCount lc L K lcReport k keep') rcReport m'' n''

/-- Same literal accepted observer and actual original membership, not a
semantic/numeric implication reflected into the object calculus. -/
theorem exact_OpenLiteralCountMembershipForward (B : Positive (Fin 1)) :
    CountMembershipForward B permutation := by
  intro α Γ left right key p m
  let H := (memberGraph right key).not
  have n : Nonempty (Derivation B (H :: Γ) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := impossibleFromGraphs left right key (withHyp p H) (withHyp m H) n
  exact ⟨Derivation.classical bad⟩

theorem exact_OpenLiteralTargetMemberLaw (B : Positive (Fin 1)) :
    TargetMemberLaw permutation B :=
  exact_OpenLiteralCountMembershipForward B

#print axioms exact_OpenLiteralCountMembershipForward
#print axioms exact_OpenLiteralTargetMemberLaw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
