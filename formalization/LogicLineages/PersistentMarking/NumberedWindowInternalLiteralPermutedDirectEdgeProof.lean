module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectSpliceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledCertificateIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreEnvelopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalAccessibilityRules (edge certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst edgeExists)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore Cut)
open NumberedWindowInternalDirectCoreEnvelopeProof (exact_OpenDCore)
open NumberedWindowInternalDirectInstalledCertificateIntroProof (exact_LiteralInstalledOddCertificateIntro)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof
  (D compare exact_LiteralRawSourceSplice exact_LiteralRawBoundarySplice)

theorem oddEdgeRename {α β : Type} (S : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge S true c x y).relabel j = edge S true c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S true c x y).subst (fun n => emb (.var (j n))) = _
  rw [edgeSubst,← termRelabelAsSubst,← termRelabelAsSubst]

/-- On the actual installed direct checker, a typed raw representative
with the source's decoded counts can use the same accepted partition
and insertion reports. The new strict edge has exactly the old target. -/
theorem exact_LiteralPermutedDirectCertificate (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (new old target witness a b : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (unary parser (suc a) new) → D B Γ (unary parser (suc b) old) →
    D B Γ (unary (typedScratch i) (suc z) a) → D B Γ (compare a b) →
    D B Γ (certificate S true c old target witness) →
    D B Γ (edge S true c new target) := by
  dsimp only
  intro newParse oldParse newTyped compareRaw held
  let S := literalData i r
  let B := sourceBody S c
  let d := dCore i r permutation
  have raw := (exact_CertificateRules i (jRaw i) r d true c B α Γ old target witness).1 held
  apply exact_OpenDCore i r permutation B α Γ old witness target _ raw
  intro β j Δ kept removed inserted keep _ _ reports
  rw [oddEdgeRename]
  have np := renameParser new a newParse j Δ keep
  have op := renameParser old b oldParse j Δ keep
  have typed := renameInto newTyped j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at typed
  have cmp := renamePair permutation (suc z) a b compareRaw j keep
  simp only [sucRelabel,zRelabel] at cmp
  let new' := new.relabel j
  let old' := old.relabel j
  let t := target.relabel j
  have cut : Cut i r permutation B Δ new' t kept removed inserted :=
    ⟨exact_LiteralRawBoundarySplice i new' old' t removed (a.relabel j) np typed reports.scalarBoundary,
      exact_LiteralRawSourceSplice new' old' kept removed (a.relabel j) (b.relabel j)
        np op cmp reports.sourceObserver,
      reports.targetObserver,reports.insertionScan⟩
  exact edgeIntroduction (exact_LiteralInstalledOddCertificateIntro i r c new' t kept removed inserted cut)

theorem exact_LiteralPermutedDirectEdge (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (new old target a b : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (unary parser (suc a) new) → D B Γ (unary parser (suc b) old) →
    D B Γ (unary (typedScratch i) (suc z) a) → D B Γ (compare a b) →
    D B Γ (edge S true c old target) → D B Γ (edge S true c new target) := by
  dsimp only
  intro newParse oldParse newTyped compareRaw held
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := certificate S true c (old.relabel j) (target.relabel j) w
  let Δ : List (Formula (α ⊕ Fin 1)) := H :: Γ.map weaken
  have keep (f : Formula α) (m : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,m,rfl⟩)
  have typed := renameInto newTyped j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at typed
  have cmp := renamePair permutation (suc z) a b compareRaw j keep
  simp only [sucRelabel,zRelabel] at cmp
  have hp : D B Δ H := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨got⟩ := exact_LiteralPermutedDirectCertificate i r c _ Δ
    (new.relabel j) (old.relabel j) (target.relabel j) w (a.relabel j) (b.relabel j)
    (renameParser new a newParse j Δ keep) (renameParser old b oldParse j Δ keep) typed cmp hp
  have out : Derivation B Δ (weaken (edge S true c new target)) := by
    rw [weaken,oddEdgeRename]
    exact got
  obtain ⟨h⟩ := held
  rw [edgeExists] at h
  exact ⟨Derivation.existentialElimination h out⟩

#print axioms exact_LiteralPermutedDirectCertificate
#print axioms exact_LiteralPermutedDirectEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectEdgeProof
