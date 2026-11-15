module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
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
open Targets AgreementSyntaxProof AgreementBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem headMember (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw head)) := by
  apply containsHit raw head tail head hc
  rw [equalEqn]
  exact ⟨InternalTagArithmeticSupportProof.refl head⟩

theorem tailAgreement (raw head tail left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement raw left right))) :
    Nonempty (Derivation body Delta (lookupAgreement tail left right)) := by
  apply agreementIntro
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let C := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (tail.relabel j) key
  let L := graph2 ExchangeMapGraph.lookup value (left.relabel j) key
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [graph2Rename] at hcj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j C
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [agreementRename] at haj
  have hm : Nonempty (Derivation body (L :: M :: C) M) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hl : Nonempty (Derivation body (L :: M :: C) L) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hmraw := PrimaryEdgeInclusion.FilterStepProof.consContainsTail (raw.relabel j) (head.relabel j) (tail.relabel j) key
    (withHyp (withHyp hcj M) L) hm
  obtain ⟨hr⟩ := agreementApply (raw.relabel j) (left.relabel j) (right.relabel j) key value
    (withHyp (withHyp haj M) L) hmraw hl
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction hr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
