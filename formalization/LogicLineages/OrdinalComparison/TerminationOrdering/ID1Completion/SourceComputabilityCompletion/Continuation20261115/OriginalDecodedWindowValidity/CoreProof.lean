module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalListCodecDecompositionSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open Targets SyntaxProof MemberBindingProof
open InductionDefinitions InductionSyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem nilMembersAt (n : Nat) (raw : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z))) :
    Nonempty (Derivation body Delta (boundedMembers n raw)) := by
  apply membersIntro
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let C := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (raw.relabel j) key
  have hzj := InternalGraphCompositionFunctionalityProof.renameInto hz j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  simp only [InternalTagArithmeticSyntaxProof.eqnRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hzj
  have hm : Nonempty (Derivation body (M :: C) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hm0 := headTransport contains (numeral 1) (raw.relabel j) z (Fin.cons key Fin.elim0) (withHyp hzj M) hm
  have hz0 := containsNil (body := body) (Delta := M :: C) key
  obtain ⟨he⟩ := valueUnique contains (suc z) z ![z,key] hm0 hz0
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply he))⟩

theorem nilCore (n : Nat) (raw : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z))) :
    Nonempty (Derivation body Delta (AtRaw n raw)) := by
  have hm := nilMembersAt n raw hz
  obtain ⟨he⟩ := hz
  have hv := headTransport (symbols n) (numeral 1) z raw Fin.elim0 ⟨symm he⟩ (StepProof.nilAccept n)
  apply andIntro
  · obtain ⟨h⟩ := withHyp hm (graph1 (symbols n) (numeral 1) raw)
    exact ⟨Derivation.implicationIntroduction h⟩
  · obtain ⟨h⟩ := withHyp hv (boundedMembers n raw)
    exact ⟨Derivation.implicationIntroduction h⟩

theorem consCore (n : Nat) (raw head tail : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
    Nonempty (Derivation body Delta (AtRaw n raw)) := by
  have hi := belowRawAt n raw tail ih (consTailDescent raw head tail hc)
  apply andIntro
  · let A := graph1 (symbols n) (numeral 1) raw
    have hv : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hs := StepProof.consRecover n raw head tail (withHyp hc A) hv
    obtain ⟨hforward⟩ := andLeft (withHyp hi A)
    obtain ⟨htail⟩ := andRight hs
    have hm : Nonempty (Derivation body (A :: Delta) (boundedMembers n tail)) :=
      ⟨Derivation.implicationElimination hforward htail⟩
    obtain ⟨hout⟩ := MemberProof.consMembers n raw head tail (withHyp hc A) (andLeft hs) hm
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let A := boundedMembers n raw
    have hm : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hh := membersApply n raw head hm
      (OriginalMapGraphTransport.RestrictionProof.headMember raw head tail (withHyp hc A))
    have ht := MemberProof.tailMembers n raw head tail (withHyp hc A) hm
    obtain ⟨hback⟩ := andRight (withHyp hi A)
    obtain ⟨ht⟩ := ht
    have hv : Nonempty (Derivation body (A :: Delta) (graph1 (symbols n) (numeral 1) tail)) :=
      ⟨Derivation.implicationElimination hback ht⟩
    obtain ⟨hout⟩ := StepProof.consAccept n raw head tail (withHyp hc A) hh hv
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem rawStep (n : Nat) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (AtRaw n raw)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · exact nilCore n raw ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta head tail hj hc
    rw [atRawRename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    rw [belowRawRename] at ihj
    exact consCore n (raw.relabel j) head tail ihj hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.CoreProof
