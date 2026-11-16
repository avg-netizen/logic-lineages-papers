module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionUseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ChildListProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open Continuation20261115 Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem predecessor (n : Nat) (fuel node param p2 p3 out bound types heads labels tupleBound : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowFuel n (suc fuel))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound fuel)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param types p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 heads p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 labels tupleBound)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (Lists.Characterizes n out bound fuel types heads labels tupleBound)) := by
  apply ListBindingProof.introduce
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let Theta := Delta.map (fun q => q.relabel j)
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hij := renameInto hi j Theta hj
  simp only [InductionSyntaxProof.belowFuelRename,sucRelabel] at hij
  have hnj := renameInto hn j Theta hj
  have hpj := renameInto hp j Theta hj
  have h2j := renameInto h2 j Theta hj
  have h3j := renameInto h3 j Theta hj
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hnj hpj h2j h3j hej
  have hc := InductionBindingProof.belowFuelAt n (suc (fuel.relabel j)) (fuel.relabel j) hij
    (InternalCoprimeMultipleBoundedProof.selfLtSucc (fuel.relabel j))
  exact InductionBindingProof.atFuelApply n (fuel.relabel j) (node.relabel j) (param.relabel j)
    (p2.relabel j) (p3.relabel j) (out.relabel j) (.var (.inr 0)) (bound.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) hc
    (andIntro (andIntro (andIntro (andIntro hnj hpj) h2j) h3j) hej)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ChildListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ChildListProof
