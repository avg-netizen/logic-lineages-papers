module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PairImageProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilImpossible (param out node : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out z param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hz := valueUnique pairRoots out z ![z,param] hv (PairRecursionProof.nilValue param)
  have hm0 := headTransport contains (numeral 1) out z (Fin.cons node Fin.elim0) hz hm
  obtain ⟨hf⟩ := valueUnique contains (numeral 1) z ![z,node] hm0 (containsNil node)
  exact ⟨sucNeZeroApply hf⟩

theorem tailLift (raw head tail param node : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (image tail param node))) :
    Nonempty (Derivation body Delta (image raw param node)) := by
  obtain ⟨hi⟩ := hi
  apply Nonempty.intro
  apply Derivation.existentialElimination hi
  let Theta : List (Formula (alpha ⊕ Fin 1)) := imageMatrix tail param node :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta ((image raw param node).relabel Sum.inl)
  rw [imageRename]
  have hw : Nonempty (Derivation body Theta (imageMatrix tail param node)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc (Sum.inl : alpha → alpha ⊕ Fin 1) Theta (by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  simp only [graph2Rename] at hcj
  have hm := NumericDependencyCross.SupportProof.memberTail (raw.relabel Sum.inl) (head.relabel Sum.inl)
    (tail.relabel Sum.inl) (.var (.inr 0)) hcj (andLeft hw)
  exact Classical.choice (introduce (raw.relabel Sum.inl) (param.relabel Sum.inl) (node.relabel Sum.inl) (.var (.inr 0)) hm (andRight hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimSupportProof
