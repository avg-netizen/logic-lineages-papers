module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSideOutcomesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedTwoSideFinishProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalChangedSideFromScratchProof (Body)
open NumberedWindowInternalScratchSideSeedProof (ScratchSideSeed relocateScratchSideSeed)
open NumberedWindowInternalCertifiedSideOutcomesProof (exact_OriginalCertifiedSideOutcomes)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (App Cmp)
open NumberedWindowInternalCertifiedOriginFinishProof (Outcome exact_OriginalCertifiedOriginFinish)
open NumberedWindowInternalLiteralSingletonProgressSyntaxProof (oddCertificateRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)

private theorem outcomeRelabel (i : Program 1) (r : Program 3) (c : Nat)
    {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}
    (b : Bool) (s t w d : OTerm α) (p : Outcome i r c Γ b s t w d)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Outcome i r c Δ b (s.relabel j) (t.relabel j) (w.relabel j) (d.relabel j) := by
  cases b
  · obtain ⟨same,eq⟩ := p
    have e := renameInto eq j Δ keep
    rw [eqnRelabel,zRelabel] at e
    exact ⟨congrArg (fun a => a.relabel j) same,e⟩
  · have q : Pr (literalData i r) c Γ (certificate (literalData i r) true c s t w) := p
    have moved := renameInto q j Δ keep
    rw [oddCertificateRename] at moved
    exact moved

/-- Select the actual unchanged or changed outcome for both components, and invoke the original continuation. -/
theorem exact_OriginalCertifiedTwoSideFinish (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (a b v : OTerm α) (goal : Formula α)
    (rawDL rawDR dsL dsR tL tR kL kR dL dR rowsL rowsR pL pR sJL sJR wholeTarget targetJoin : OTerm α)
    (l : ScratchSideSeed i r c Γ a rawDL dsL tL kL dL rowsL pL sJL)
    (r' : ScratchSideSeed i r c Γ b rawDR dsR tR kR dR rowsR pR sJR)
    (no : Pr (literalData i r) c Γ ((eqn dL z ⊓ eqn dR z).not))
    (vParse : Pr (literalData i r) c Γ (unary parser (suc wholeTarget) v))
    (app : Pr (literalData i r) c Γ (App tL tR targetJoin))
    (cmp : Pr (literalData i r) c Γ (Cmp wholeTarget targetJoin))
    (cases : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  let B := Body i r c
  apply exact_OriginalCertifiedSideOutcomes i r c a rawDL dsL tL kL dL rowsL pL sJL goal l
  intro β j Δ bL rawL wL pl keep lparse lcount lo
  have movedR := relocateScratchSideSeed i r c r' j keep
  apply exact_OriginalCertifiedSideOutcomes i r c (b.relabel j) (rawDR.relabel j)
    (dsR.relabel j) (tR.relabel j) (kR.relabel j) (dR.relabel j)
    (rowsR.relabel j) (pR.relabel j) (sJR.relabel j) (goal.relabel j) movedR
  intro γ k Ω bR rawR wR pr carry rparse rcount ro
  let ρ := k ∘ j
  have stay := keepThrough j k keep carry
  have np := renameInto no ρ Ω stay
  change Nonempty (Derivation B Ω ((eqn dL z ⊓ eqn dR z).relabel ρ).not) at np
  rw [conjunctionRename,eqnRelabel,eqnRelabel,zRelabel] at np
  have vp := renameParser v wholeTarget vParse ρ Ω stay
  have lp := renameParser rawL pl lparse k Ω carry
  have ap := renamePair append targetJoin tL tR app ρ stay
  have obs : Nonempty (Derivation B Ω (Cmp (wholeTarget.relabel ρ) (targetJoin.relabel ρ))) := by
    simpa only [Cmp,sucRelabel,zRelabel] using
      renamePair permutation (suc z) wholeTarget targetJoin cmp ρ stay
  have leftCmp : Nonempty (Derivation B Ω (Cmp (tL.relabel ρ) (pl.relabel k))) := by
    simpa only [Cmp,sucRelabel,zRelabel,ρ,← Term.relabel_relabel] using
      renamePair permutation (suc z) (tL.relabel j) pl lcount k carry
  have rightCmp : Nonempty (Derivation B Ω (Cmp (tR.relabel ρ) pr)) := by
    simpa only [ρ,← Term.relabel_relabel] using rcount
  have leftOut : Outcome i r c Ω bL (a.relabel ρ) (rawL.relabel k) (wL.relabel k) (dL.relabel ρ) := by
    simpa only [ρ,← Term.relabel_relabel] using
      outcomeRelabel i r c bL (a.relabel j) rawL wL (dL.relabel j) lo k carry
  have rightOut : Outcome i r c Ω bR (b.relabel ρ) rawR wR (dR.relabel ρ) := by
    simpa only [ρ,← Term.relabel_relabel] using ro
  rw [formulaRelabelComposition j k goal]
  exact exact_OriginalCertifiedOriginFinish i r c ρ a b v goal
    (rawL.relabel k) rawR (wL.relabel k) wR (dL.relabel ρ) (dR.relabel ρ)
    (tL.relabel ρ) (tR.relabel ρ) (targetJoin.relabel ρ) (pl.relabel k) pr
    (wholeTarget.relabel ρ) bL bR stay np vp lp rparse ap obs leftCmp rightCmp leftOut rightOut cases

#print axioms exact_OriginalCertifiedTwoSideFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedTwoSideFinishProof
