module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossIntroCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossIntroProof
open OriginalTypeListsEnumeration
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
open CrossIntroInductionDefinitions CrossIntroInductionSyntaxProof CrossIntroBindingProof
open OriginalTypeListsEnumeration (cross)

theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 5) := raw.relabel Sum.inl
  let param : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let node : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let a : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let b : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let Theta := fields r param out node a b :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r param out node a b)
  have hf : Nonempty (Derivation body Theta (fields r param out node a b)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 5) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (CrossIntroCoreProof.core r param out node a b ihj (andLeft (andLeft hf)) (andRight (andLeft hf)) (andRight hf))

theorem introduce (raw param out node a b : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 cross out raw param)))
    (hm : Nonempty (Derivation body Delta ((graph2 contains (numeral 1) raw a ⊓ graph2 contains (numeral 1) param b))))
    (hq : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode node a b))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) :=
  atRawApply raw param out node a b (rawInduction raw (fun _ _ r h => rawStep r h)) (andIntro (andIntro hv hm) hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossIntroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossIntroProof
