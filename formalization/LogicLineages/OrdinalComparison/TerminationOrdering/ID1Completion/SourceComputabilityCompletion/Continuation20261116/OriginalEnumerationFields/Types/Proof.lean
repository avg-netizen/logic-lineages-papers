module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261115.OriginalTypeListsMembership.Targets (allMembers)
open SyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atAllowed (raw allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (result raw allowed)) := by
  let G := graph2 allTypes (suc z) raw allowed
  let M := allMembers raw allowed
  obtain ⟨hf⟩ := CoreProof.coreForward raw allowed (withHyp ih G)
    (show Nonempty (Derivation body (G :: Delta) G) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := CoreProof.coreBackward raw allowed (withHyp ih M)
    (show Nonempty (Derivation body (M :: Delta) M) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 1) (Delta.map (fun q => q.relabel Sum.inl))
    (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [belowRawRename] at ihj
  exact atAllowed (raw.relabel Sum.inl) (.var (.inr 0)) ihj

theorem equivalence (raw allowed : OTerm alpha) :
    (Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed)) ↔
     Nonempty (Derivation body Delta (allMembers raw allowed))) := by
  have h := atRawApply raw allowed (rawInduction raw (fun _ _ r ih => step r ih)) (body := body) (Delta := Delta)
  constructor
  · intro hg
    obtain ⟨hf⟩ := andLeft h
    obtain ⟨hg⟩ := hg
    exact ⟨Derivation.implicationElimination hf hg⟩
  · intro hm
    obtain ⟨hb⟩ := andRight h
    obtain ⟨hm⟩ := hm
    exact ⟨Derivation.implicationElimination hb hm⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Proof
