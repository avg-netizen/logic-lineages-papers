module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthBoundProof
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
open DepthSyntaxProof
open Continuation20261115
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem introduce (n : Nat) (raw fuel d : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) d raw)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess d (suc fuel)))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw fuel)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Delta (depthMatrix n raw fuel) (fun _ => InternalTagArithmeticSyntaxProof.emb d)
  rw [depthWitness]
  exact andIntro hd hb

theorem observedBound (n : Nat) (raw fuel d : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) d raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n raw fuel))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess d (suc fuel))) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Delta (depthMatrix n raw fuel)
    (InternalLessThan.strictLess d (suc fuel)) hb
  let Theta := depthMatrix n raw fuel :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta (depthMatrix n raw fuel)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hdj := renameInto hd (Sum.inl : alpha → alpha ⊕ Fin 1) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [graph1Rename] at hdj
  rw [strictRename,sucRelabel]
  have he := valueUnique (OriginalEnumerationDepth.depth n) (d.relabel Sum.inl) (.var (.inr 0))
    (Fin.cons (raw.relabel Sum.inl) Fin.elim0) hdj (andLeft hf)
  exact InternalOriginalPairingOrderArithmeticProof.strictTransport (d.relabel Sum.inl) (suc (fuel.relabel Sum.inl))
    (.var (.inr 0)) (suc (fuel.relabel Sum.inl)) he ⟨refl _⟩ (andRight hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthBoundProof
