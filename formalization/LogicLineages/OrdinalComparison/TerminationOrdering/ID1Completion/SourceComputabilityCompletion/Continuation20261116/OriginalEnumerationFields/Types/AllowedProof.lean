module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open Continuation20261115.OriginalTypeListsMembership.Targets (allMembers)
open OriginalContextInsertionSyntaxProof (lengthRename)
open AllowedSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem introduce (types allowed bound len : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess len (suc bound))))
    (hm : Nonempty (Derivation body Delta (allMembers types allowed))) :
    Nonempty (Derivation body Delta (Targets.typesAllowed types allowed bound)) := by
  have hlength : Nonempty (Derivation body Delta (InternalFiniteBlocks.block (lengthMatrix types bound))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 1 Delta (lengthMatrix types bound) (fun _ => InternalTagArithmeticSyntaxProof.emb len)
    rw [lengthWitness]
    exact andIntro hl hb
  exact andIntro hlength hm

theorem lengthBound (types allowed bound len : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types)))
    (ha : Nonempty (Derivation body Delta (Targets.typesAllowed types allowed bound))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess len (suc bound))) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Delta (lengthMatrix types bound)
    (InternalLessThan.strictLess len (suc bound)) (andLeft ha)
  let Theta := lengthMatrix types bound :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta (lengthMatrix types bound)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hlj := renameInto hl (Sum.inl : alpha → alpha ⊕ Fin 1) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [lengthRename] at hlj
  rw [strictRename,sucRelabel]
  have he := valueUnique OriginalContextInsertion.length (len.relabel Sum.inl) (.var (.inr 0))
    (Fin.cons (types.relabel Sum.inl) Fin.elim0) hlj (andLeft hf)
  exact InternalOriginalPairingOrderArithmeticProof.strictTransport (len.relabel Sum.inl) (suc (bound.relabel Sum.inl))
    (.var (.inr 0)) (suc (bound.relabel Sum.inl)) he ⟨refl _⟩ (andRight hf)

theorem members (types allowed bound : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (Targets.typesAllowed types allowed bound))) :
    Nonempty (Derivation body Delta (allMembers types allowed)) := andRight ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedProof
