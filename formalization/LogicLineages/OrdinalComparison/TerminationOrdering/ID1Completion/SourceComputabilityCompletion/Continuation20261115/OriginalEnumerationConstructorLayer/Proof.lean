module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.ObservationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem backward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (layer n) out xs)))
    (hw : Nonempty (Derivation body Delta (InternalFiniteBlocks.block (Targets.witnessMatrix n xs code)))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply InternalFiniteBlocksProof.elimination body alpha 8 Delta (Targets.witnessMatrix n xs code) _ hw
  let j : alpha → alpha ⊕ Fin 8 := Sum.inl
  let ys : Fin 8 → OTerm (alpha ⊕ Fin 8) := fun i => .var (.inr i)
  let Theta := Targets.witnessMatrix n xs code :: Delta.map (fun q => q.relabel j)
  have hf : Nonempty (Derivation body Theta (Targets.witnessMatrix n xs code)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [programRename] at hgj
  rw [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  exact ObservationsProof.atComponents n (fun i => (xs i).relabel j) ys (out.relabel j) (code.relabel j)
    hgj (andLeft hf) (andRight hf)

theorem internalMembership : Targets.InternalMembership := by
  intro body alpha Delta n xs out code hg
  constructor
  · exact ObservationsProof.forward n xs out code hg
  · exact backward n xs out code hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Proof
