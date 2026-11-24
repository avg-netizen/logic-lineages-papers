module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSwapProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralCountAppendSwapProof (exact_LiteralAppendSwap)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalOriginKeptSplitTargets
open NumberedWindowInternalOriginKeptSplitCasesProof (exact_OriginalKeptSplitCases)
open NumberedWindowInternalOriginKeptNilProof (packSplit)
open NumberedWindowInternalOriginKeptInductionSyntaxProof (splitRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev App (l r out : OTerm α) : Formula α := programGraph append out ![l,r]

private theorem evidenceRename {β : Type} (l r k d : OTerm α) (w : Fin 8 → OTerm α) (j : α → β) :
    (evidence l r k d w).relabel j =
      evidence (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) (fun i => (w i).relabel j) := by
  simp only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel]

private theorem swapPiece (s l r lr rl : OTerm α)
    (held : Nonempty (Derivation B Γ (piece s l r lr)))
    (swapped : Nonempty (Derivation B Γ (App r l rl))) :
    Nonempty (Derivation B Γ (piece s r l rl)) := by
  obtain ⟨p⟩ := held
  have m := exact_LiteralAppendSwap l r lr rl ⟨Derivation.conjunctionLeft p⟩ swapped
  obtain ⟨n⟩ := exact_LiteralObserverTransitivity s lr rl ⟨Derivation.conjunctionRight p⟩ m
  obtain ⟨a⟩ := swapped
  exact ⟨Derivation.conjunctionIntroduction a n⟩

/-- Reassemble an opened witness vector under two actual reverse-order
joins while leaving the underlying four allocated tapes untouched. -/
theorem exact_OriginalKeptSwapEvidence (l r k d rk rd : OTerm α) (w : Fin 8 → OTerm α)
    (held : Nonempty (Derivation B Γ (evidence l r k d w)))
    (kept : Nonempty (Derivation B Γ (App (w 2) (w 0) rk)))
    (removed : Nonempty (Derivation B Γ (App (w 3) (w 1) rd))) :
    Nonempty (Derivation B Γ (evidence r l k d ![w 2,w 3,w 0,w 1,w 5,w 4,rk,rd])) := by
  obtain ⟨e⟩ := held
  let tail := Derivation.conjunctionRight e
  let both := Derivation.conjunctionRight tail
  obtain ⟨p⟩ := swapPiece k (w 0) (w 2) (w 6) rk ⟨Derivation.conjunctionLeft both⟩ kept
  obtain ⟨q⟩ := swapPiece d (w 1) (w 3) (w 7) rd ⟨Derivation.conjunctionRight both⟩ removed
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft tail)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft e)
      (Derivation.conjunctionIntroduction p q))⟩

theorem exact_OriginalKeptSwapOpened (l r k d : OTerm α) (w : Fin 8 → OTerm α)
    (held : Nonempty (Derivation B Γ (evidence l r k d w))) :
    Nonempty (Derivation B Γ (splitExists r l k d)) := by
  apply programCases append ![w 2,w 0] (splitExists r l k d)
  intro β j Δ rk keep kp
  rw [binaryInputsRename] at kp
  rw [splitRename]
  apply programCases append ![(w 3).relabel j,(w 1).relabel j]
    (splitExists (r.relabel j) (l.relabel j) (k.relabel j) (d.relabel j))
  intro γ t Ω rd carry dp
  rw [binaryInputsRename] at dp
  rw [splitRename]
  let ρ := t ∘ j
  have kee := keepThrough j t keep carry
  have old := renameInto held ρ Ω kee
  rw [evidenceRename] at old
  have rkRel := renameInto kp t Ω carry
  have rj : Nonempty (Derivation B Ω (App ((w 2).relabel ρ) ((w 0).relabel ρ) (rk.relabel t))) := by
    simpa only [App,programRename,binaryInputsRename,ρ,← Term.relabel_relabel] using rkRel
  have dj : Nonempty (Derivation B Ω (App ((w 3).relabel ρ) ((w 1).relabel ρ) rd)) := by
    simpa only [App,ρ,← Term.relabel_relabel] using dp
  let W : Fin 8 → OTerm γ := fun i => (w i).relabel ρ
  have ev := exact_OriginalKeptSwapEvidence (l.relabel ρ) (r.relabel ρ) (k.relabel ρ) (d.relabel ρ)
    (rk.relabel t) rd W old rj dj
  simpa only [ρ,← Term.relabel_relabel] using
    packSplit (r.relabel ρ) (l.relabel ρ) (k.relabel ρ) (d.relabel ρ)
      ![W 2,W 3,W 0,W 1,W 5,W 4,rk.relabel t,rd] ev

/-- Physical symmetry of the oriented source allocation, not raw append
commutativity: the two actual new joins are compared by exact counts. -/
theorem exact_OriginalKeptSplitSwap (l r k d : OTerm α)
    (held : Nonempty (Derivation B Γ (splitExists l r k d))) :
    Nonempty (Derivation B Γ (splitExists r l k d)) := by
  apply exact_OriginalKeptSplitCases l r k d (splitExists r l k d) held
  intro β j Δ w keep e
  rw [splitRename]
  exact exact_OriginalKeptSwapOpened (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) w e

#print axioms exact_OriginalKeptSwapEvidence
#print axioms exact_OriginalKeptSwapOpened
#print axioms exact_OriginalKeptSplitSwap
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSwapProof
