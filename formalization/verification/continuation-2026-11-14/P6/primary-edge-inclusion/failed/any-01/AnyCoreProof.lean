module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Any AnySyntaxProof AnyBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consCore (E : Program 3) (raw head tail source candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (he : Nonempty (Derivation body Delta (graph3 E (suc z) source candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw source))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  let A := equal head source
  apply formulaCases A
  · have hh : Nonempty (Derivation body (A :: Delta) (eqn source head)) := by
      have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      rw [equalEqn] at h
      obtain ⟨h⟩ := h
      exact ⟨symm h⟩
    have hedge := headTransport E (suc z) source head ![candidate,parameter] hh (withHyp he A)
    exact AnyStepProof.consHit E raw head tail candidate parameter (withHyp hc A) hedge
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover raw head tail source (suc z)
      (withHyp hc A.not) hn (withHyp hm A.not)
    have hi := belowRawApply E raw tail source candidate parameter (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not)) (andIntro ht (withHyp he A.not))
    exact AnyStepProof.consTail E raw head tail candidate parameter (withHyp hc A.not) hi

theorem nonzeroAt (E : Program 3) (raw head source candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (ha : Nonempty (Derivation body Delta (graph3 E (suc z) source candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw source))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj ht
  rw [resultRename]
  simp only [consTermRename,emptyRename] at ht
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [nonzeroRename] at hn'
  have hh' := renameInto hh j Theta hj
  rw [graph1Rename] at hh'
  have ha' := renameInto ha j Theta hj
  simp only [graph3Rename,sucRelabel,zRelabel] at ha'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  exact consCore E (raw.relabel j) (head.relabel j) tail (source.relabel j) (candidate.relabel j)
    (parameter.relabel j) hb' (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) ha' hm'

theorem nonzeroCore (E : Program 3) (raw source candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (ha : Nonempty (Derivation body Delta (graph3 E (suc z) source candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw source))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hh
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [nonzeroRename] at hn'
  have ha' := renameInto ha j Theta hj
  simp only [graph3Rename,sucRelabel,zRelabel] at ha'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  exact nonzeroAt E (raw.relabel j) head (source.relabel j) (candidate.relabel j)
    (parameter.relabel j) hb' hn' hh ha' hm'

theorem core (E : Program 3) (raw source candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (ha : Nonempty (Derivation body Delta (graph3 E (suc z) source candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw source))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  let A := eqn raw z
  apply formulaCases A
  · exact PrimaryExpansion.PreservationCoreProof.zeroCore raw source _ ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A)
  · exact nonzeroCore E raw source candidate parameter (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A.not) (withHyp hm A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyCoreProof
