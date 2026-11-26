module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimSupportProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open MapImageProof
variable (F : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilValue : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) z z)) :=
  InternalRawListRecursionProof.nilValue (InternalRawListRecursion.zero : Program 0)
    (InternalListMap.mapStep F) z Fin.elim0
    (InternalAcceptanceConjunctionProof.constantZeroValue Fin.elim0)

theorem nilImpossible (out node : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hz := valueUnique (InternalListMap.map F) out z ![z] hv (nilValue F)
  have hm0 := headTransport contains (numeral 1) out z (Fin.cons node Fin.elim0) hz hm
  obtain ⟨hf⟩ := valueUnique contains (numeral 1) z ![z,node] hm0 (containsNil node)
  exact ⟨sucNeZeroApply hf⟩

theorem tailLift (raw head tail node : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (image F tail node))) :
    Nonempty (Derivation body Delta (image F raw node)) := by
  obtain ⟨hi⟩ := hi
  apply Nonempty.intro
  apply Derivation.existentialElimination hi
  let Theta : List (Formula (alpha ⊕ Fin 1)) := imageMatrix F tail node :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta ((image F raw node).relabel Sum.inl)
  rw [imageRename]
  have hw : Nonempty (Derivation body Theta (imageMatrix F tail node)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc (Sum.inl : alpha → alpha ⊕ Fin 1) Theta (by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  simp only [graph2Rename] at hcj
  have hm := NumericDependencyCross.SupportProof.memberTail (raw.relabel Sum.inl) (head.relabel Sum.inl)
    (tail.relabel Sum.inl) (.var (.inr 0)) hcj (andLeft hw)
  exact Classical.choice (introduce F (raw.relabel Sum.inl) (node.relabel Sum.inl) (.var (.inr 0)) hm (andRight hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimSupportProof
