module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalAcceptanceSupportProof (programCases)
open OriginalContextInsertionSyntaxProof (lengthRename)
open InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilResult (bound allowed out types len rows : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn types z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types))) :
    Nonempty (Derivation body Delta (result (suc bound) allowed out types len)) := by
  have hcond := BaseProof.nilCondition (suc bound) allowed types len hz hl
  obtain ⟨hz⟩ := hz
  have hm := containsHit out z rows types ho (by rw [equalEqn]; exact ⟨symm hz⟩)
  have forward := withHyp hcond (graph2 contains (numeral 1) out types)
  have backward := withHyp hm (condition (suc bound) allowed types len)
  obtain ⟨hf⟩ := forward
  obtain ⟨hb⟩ := backward
  exact andIntro ⟨Derivation.implicationIntroduction hf⟩ ⟨Derivation.implicationIntroduction hb⟩

theorem atCons (bound allowed out types len previous rows head tail : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration previous bound allowed)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.cross rows allowed previous)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types head tail))) :
    Nonempty (Derivation body Delta (result (suc bound) allowed out types len)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
  intro beta j Theta tailLen hj htl
  simp only [consTermRename,emptyRename] at htl
  rw [resultRename]
  simp only [sucRelabel]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [rowRename] at ihj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename] at hcj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,zRelabel] at hoj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [lengthRename] at hlj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename] at htj
  exact StepValuesProof.atCons (bound.relabel j) (allowed.relabel j) (out.relabel j)
    (types.relabel j) (len.relabel j) (previous.relabel j) (rows.relabel j)
    (head.relabel j) (tail.relabel j) tailLen ihj hpj hcj hoj hlj htj htl

theorem atLists (bound allowed out types len previous rows : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration previous bound allowed)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.cross rows allowed previous)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types))) :
    Nonempty (Derivation body Delta (result (suc bound) allowed out types len)) := by
  apply OriginalContextInsertionLengthProof.listCases types _
  · exact nilResult bound allowed out types len rows ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ho _) (withHyp hl _)
  · intro beta j Theta head tail hj ht
    rw [resultRename]
    simp only [sucRelabel]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [rowRename] at ihj
    have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
    simp only [graph2Rename] at hpj
    have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
    simp only [graph2Rename] at hcj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    simp only [graph2Rename,zRelabel] at hoj
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    simp only [lengthRename] at hlj
    exact atCons (bound.relabel j) (allowed.relabel j) (out.relabel j)
      (types.relabel j) (len.relabel j) (previous.relabel j) (rows.relabel j)
      head tail ihj hpj hcj hoj hlj ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepProof
