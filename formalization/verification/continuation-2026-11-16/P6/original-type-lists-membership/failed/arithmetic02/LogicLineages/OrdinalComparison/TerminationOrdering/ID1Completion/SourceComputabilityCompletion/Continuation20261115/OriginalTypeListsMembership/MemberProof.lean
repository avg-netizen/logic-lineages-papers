module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114
open Targets MemberSyntaxProof MemberBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalPositiveUnfoldingSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
theorem nilMembers (allowed : OTerm alpha) : Nonempty (Derivation body Delta (allMembers z allowed)) := by
  apply membersIntro
  simp only [memberMatrix, InternalTagArithmeticSyntaxProof.zRelabel]
  let key : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let C : List (Formula (alpha ⊕ Fin 1)) := Delta.map (fun q => q.relabel Sum.inl)
  let M := graph2 contains (numeral 1) z key
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := containsNil (body := body) (Delta := M :: C) key
  obtain ⟨he⟩ := valueUnique contains (suc z) z ![z,key] hm hz
  have hf := sucNeZeroApply he
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩

theorem tailMembers (raw head tail allowed : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (allMembers raw allowed))) :
    Nonempty (Derivation body Delta (allMembers tail allowed)) := by
  apply membersIntro
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let C := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (tail.relabel j) key
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [graph2Rename] at hcj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [membersRename] at haj
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hmraw := PrimaryEdgeInclusion.FilterStepProof.consContainsTail (raw.relabel j) (head.relabel j) (tail.relabel j) key (withHyp hcj M) hm
  obtain ⟨hr⟩ := membersApply (raw.relabel j) (allowed.relabel j) key (withHyp haj M) hmraw
  exact ⟨Derivation.implicationIntroduction hr⟩

theorem consMemberBound (raw head tail allowed key : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed head)))
    (ht : Nonempty (Derivation body Delta (allMembers tail allowed)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw key))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed key)) := by
  apply formulaCases (eqn head key)
  · let A := eqn head key
    have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact InternalApplicationValidityStackAppendRunProof.rightTransport contains (numeral 1)
      allowed head key he (withHyp hh A)
  · let A := (eqn head key).not
    have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm' := PrimaryMembership.Proof.missRecover raw head tail key (numeral 1) (withHyp hc A) (by simpa only [equalEqn] using hn) (withHyp hm A)
    exact membersApply tail allowed key (withHyp ht A) hm'

theorem consMembers (raw head tail allowed : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed head)))
    (ht : Nonempty (Derivation body Delta (allMembers tail allowed))) :
    Nonempty (Derivation body Delta (allMembers raw allowed)) := by
  apply membersIntro
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let C := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (raw.relabel j) key
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [graph2Rename] at hcj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hhj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [membersRename] at htj
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consMemberBound (raw.relabel j) (head.relabel j) (tail.relabel j) (allowed.relabel j) key
    (withHyp hcj M) (withHyp hhj M) (withHyp htj M) hm
  exact ⟨Derivation.implicationIntroduction h⟩

theorem headMember (raw head tail allowed : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (allMembers raw allowed))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed head)) := by
  apply membersApply raw allowed head ha
  apply containsHit raw head tail head hc
  rw [equalEqn]
  exact ⟨refl head⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
