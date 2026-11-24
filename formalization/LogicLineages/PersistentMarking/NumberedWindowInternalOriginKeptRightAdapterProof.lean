module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSwapProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptRightAdapterProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalOriginKeptSplitTargets
open NumberedWindowInternalOriginKeptSwapProof
open NumberedWindowInternalOriginKeptInductionSyntaxProof (splitRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)

attribute [local irreducible] programGraph

/-- The local LEFT method uses the chosen occurrence in the already
opened left-removed tape. It is not general origin or split existence. -/
def LeftOpenedSupply (B : Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (l r k h t d e : OTerm α) (w : Fin 8 → OTerm α),
    Nonempty (Derivation B Γ (consGraph k h t)) →
    Nonempty (Derivation B Γ (consGraph e h d)) →
    Nonempty (Derivation B Γ (evidence l r t e w)) →
    Nonempty (Derivation B Γ (memberGraph (w 1) h)) →
    Nonempty (Derivation B Γ (splitExists l r k d))

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem evidenceRename {β : Type} (l r k d : OTerm α) (w : Fin 8 → OTerm α) (j : α → β) :
    (evidence l r k d w).relabel j =
      evidence (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j) (fun i => (w i).relabel j) := by
  simp only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel]

private theorem useSwapped (leftMethod : LeftOpenedSupply B)
    (l r k h t d e rk rd : OTerm α) (w : Fin 8 → OTerm α)
    (hk : Nonempty (Derivation B Γ (consGraph k h t)))
    (hd : Nonempty (Derivation B Γ (consGraph e h d)))
    (old : Nonempty (Derivation B Γ (evidence l r t e w)))
    (selected : Nonempty (Derivation B Γ (memberGraph (w 3) h)))
    (kept : Nonempty (Derivation B Γ (App (w 2) (w 0) rk)))
    (removed : Nonempty (Derivation B Γ (App (w 3) (w 1) rd))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  let W : Fin 8 → OTerm α := ![w 2,w 3,w 0,w 1,w 5,w 4,rk,rd]
  have opened : Nonempty (Derivation B Γ (evidence r l t e W)) :=
    exact_OriginalKeptSwapEvidence l r t e rk rd w old kept removed
  have hm : Nonempty (Derivation B Γ (memberGraph (W 1) h)) := selected
  have s := leftMethod α Γ r l k h t d e W hk hd opened hm
  exact exact_OriginalKeptSplitSwap r l k d s

/-- Move a genuine right-removed occurrence by real reversed append
outputs and the same LEFT supplier on the same tape. The final
existential is reoriented using original object split symmetry. -/
theorem exact_OriginalKeptMoveRightOpened (leftMethod : LeftOpenedSupply B)
    (l r k h t d e : OTerm α) (w : Fin 8 → OTerm α)
    (hk : Nonempty (Derivation B Γ (consGraph k h t)))
    (hd : Nonempty (Derivation B Γ (consGraph e h d)))
    (old : Nonempty (Derivation B Γ (evidence l r t e w)))
    (selected : Nonempty (Derivation B Γ (memberGraph (w 3) h))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  apply programCases append ![w 2,w 0] (splitExists l r k d)
  intro β j Δ rk keep kp
  rw [binaryInputsRename] at kp
  rw [splitRename]
  apply programCases append ![(w 3).relabel j,(w 1).relabel j]
    (splitExists (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j))
  intro γ p Ω rd carry dp
  rw [binaryInputsRename] at dp
  rw [splitRename]
  let ρ := p ∘ j
  have keepAll := keepThrough j p keep carry
  have held := renameInto old ρ Ω keepAll
  rw [evidenceRename] at held
  have hk' := renameInto hk ρ Ω keepAll
  have hd' := renameInto hd ρ Ω keepAll
  rw [consGraphRename] at hk' hd'
  have m := renameInto selected ρ Ω keepAll
  simp only [memberGraph,programRename,binaryInputsRename,sucRelabel,zRelabel] at m
  have rkRel := renameInto kp p Ω carry
  have rj : Nonempty (Derivation B Ω (App ((w 2).relabel ρ) ((w 0).relabel ρ) (rk.relabel p))) := by
    simpa only [App,programRename,binaryInputsRename,ρ,← Term.relabel_relabel] using rkRel
  have dj : Nonempty (Derivation B Ω (App ((w 3).relabel ρ) ((w 1).relabel ρ) rd)) := by
    simpa only [App,ρ,← Term.relabel_relabel] using dp
  let W : Fin 8 → OTerm γ := fun i => (w i).relabel ρ
  simpa only [ρ,← Term.relabel_relabel] using
    useSwapped leftMethod (l.relabel ρ) (r.relabel ρ) (k.relabel ρ) (h.relabel ρ)
      (t.relabel ρ) (d.relabel ρ) (e.relabel ρ) (rk.relabel p) rd W hk' hd' held m rj dj

#print axioms exact_OriginalKeptMoveRightOpened
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptRightAdapterProof
