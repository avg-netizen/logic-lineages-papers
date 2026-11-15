module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open MapIntroInductionDefinitions MapIntroInductionSyntaxProof MapIntroBindingProof
variable (F : Program 1)

theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw))) :
    Nonempty (Derivation body Delta (AtRaw F raw)) := by
  apply atRawIntro F raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 5) := raw.relabel Sum.inl
  let param : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let node : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let a : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let b : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let Theta := fields F r param out node a b :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result F r param out node a b)
  have hf : Nonempty (Derivation body Theta (fields F r param out node a b)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 5) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (MapIntroCoreProof.core F r param out node a b ihj (andLeft (andLeft hf)) (andRight (andLeft hf)) (andRight hf))

theorem introduce (raw param out node a b : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph1 F node b))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) :=
  atRawApply F raw param out node a b (rawInduction F raw (fun _ _ r h => rawStep F r h)) (andIntro (andIntro hv hm) hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
