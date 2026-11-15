module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberProof
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
open Targets SyntaxProof MemberBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalPositiveUnfoldingSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
theorem nilMembers (n : Nat) : Nonempty (Derivation body Delta (boundedMembers n z)) := by
  apply membersIntro
  let key : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let C : List (Formula (alpha ⊕ Fin 1)) := Delta.map (fun q => q.relabel Sum.inl)
  let M := graph2 contains (numeral 1) z key
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := containsNil (body := body) (Delta := M :: C) key
  obtain ⟨he⟩ := valueUnique contains (suc z) z ![z,key] hm hz
  have hf := sucNeZeroApply he
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩

theorem tailMembers (n : Nat) (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (boundedMembers n raw))) :
    Nonempty (Derivation body Delta (boundedMembers n tail)) := by
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
  obtain ⟨hr⟩ := membersApply n (raw.relabel j) key (withHyp haj M) hmraw
  exact ⟨Derivation.implicationIntroduction hr⟩

theorem consMemberBound (n : Nat) (raw head tail key : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (InternalLessThan.strictLess head (numeral n))))
    (ht : Nonempty (Derivation body Delta (boundedMembers n tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw key))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess key (numeral n))) := by
  apply formulaCases (eqn head key)
  · let A := eqn head key
    have he : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlt := InternalLessThanSupportProof.acceptOfLess head (numeral n) (withHyp hh A)
    have hv := headTransport InternalLessThan.ltTest (suc z) head key (Fin.cons (numeral n) Fin.elim0) he hlt
    exact InternalLessThanProof.lessOfAcceptance key (numeral n) hv
  · let A := (eqn head key).not
    have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm' := PrimaryMembership.Proof.missRecover raw head tail key (numeral 1) (withHyp hc A) (by simpa only [equalEqn] using hn) (withHyp hm A)
    exact membersApply n tail key (withHyp ht A) hm'

theorem consMembers (n : Nat) (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (InternalLessThan.strictLess head (numeral n))))
    (ht : Nonempty (Derivation body Delta (boundedMembers n tail))) :
    Nonempty (Derivation body Delta (boundedMembers n raw)) := by
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
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename,GuardedSourceSyntaxProof.numeralRename] at hhj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [membersRename] at htj
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consMemberBound n (raw.relabel j) (head.relabel j) (tail.relabel j) key
    (withHyp hcj M) (withHyp hhj M) (withHyp htj M) hm
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberProof
