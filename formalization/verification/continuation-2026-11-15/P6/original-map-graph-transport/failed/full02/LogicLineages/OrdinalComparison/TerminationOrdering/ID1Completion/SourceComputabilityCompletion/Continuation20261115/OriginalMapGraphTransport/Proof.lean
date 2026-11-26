module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InductionDefinitions InductionSyntaxProof BindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 3) := raw.relabel Sum.inl
  let left : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields r left right out :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r left right out)
  have hf : Nonempty (Derivation body Theta (fields r left right out)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 3) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (CoreProof.core r left right out ihj (andLeft hf) (andRight hf))

theorem transport : Targets.InternalTransport := by
  intro body alpha Delta keys left right out ha hv
  exact atRawApply keys left right out (rawInduction keys (fun _ _ r h => rawStep r h)) (andIntro ha hv)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Proof
