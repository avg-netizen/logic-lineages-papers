module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyCoreProof
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
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof InternalAcceptanceConjunctionProof
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Any AnySyntaxProof AnyBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consAt (E : Program 3) (raw head tail candidate parameter rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) rest tail candidate parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 (PrimaryExpansion.anyStep E) (suc z) head rest candidate parameter))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,candidate,parameter]
  let query : Program 4 := .composition E ![.projection 0,.projection 2,.projection 3]
  let A := programGraph query (suc z) xs
  apply formulaCases A
  · have he : Nonempty (Derivation body (A :: Delta) (graph3 E (suc z) head candidate parameter)) := by
      apply compositionRecover E ![.projection 0,.projection 2,.projection 3] (suc z) xs
        ![head,candidate,parameter] ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro i
      exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs)
        (Fin.cases (projectionValue 3 xs) (fun j => Fin.elim0 j))) i
    have hself : Nonempty (Derivation body (A :: Delta) (equal head head)) := by
      rw [equalEqn]
      exact ⟨refl head⟩
    exact WitnessProof.introduction E raw candidate parameter head
      (containsHit raw head tail head (withHyp hc A) hself) he
  · have hp := zeroBranchElim (normalize query) (.projection 1) (InternalLessThan.constantOne 4)
      (suc z) xs (normalizeReject query xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hs A.not)
    obtain ⟨hu⟩ := valueUnique (.projection (1 : Fin 4)) (suc z) rest xs hp (projectionValue 1 xs)
    have ht := outputTransport (PrimaryExpansion.anyEdge E) rest (suc z) ![tail,candidate,parameter]
      ⟨symm hu⟩ (withHyp hr A.not)
    have hi := belowRawApply E raw tail candidate parameter (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not)) ht
    exact WitnessProof.prepend E raw head tail candidate parameter (withHyp hc A.not) hi

theorem consCore (E : Program 3) (raw head tail candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) raw candidate parameter))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  have hstep := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.anyStep E) raw head tail (suc z) ![candidate,parameter] hc ha
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.anyStep E) (suc z) head tail ![candidate,parameter] _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  have hparams : (fun i => (![candidate,parameter] i).relabel j) =
      Fin.cons (candidate.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hparams] at hr hs
  simp only [sucRelabel,zRelabel] at hs
  have hr' : Nonempty (Derivation body Theta (graph3 (PrimaryExpansion.anyEdge E) rest
      (tail.relabel j) (candidate.relabel j) (parameter.relabel j))) := by
    simpa only [graph3,programGraph,PrimaryExpansion.anyEdge,InternalRawListRecursion.recGraph] using hr
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact consAt E (raw.relabel j) (head.relabel j) (tail.relabel j) (candidate.relabel j)
    (parameter.relabel j) rest hb' hc' hr' hs

theorem nonzeroAt (E : Program 3) (raw head candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) raw candidate parameter))) :
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
  exact consCore E (raw.relabel j) (head.relabel j) tail (candidate.relabel j)
    (parameter.relabel j) hb' (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) ha'

theorem nonzeroCore (E : Program 3) (raw candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) raw candidate parameter))) :
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
  exact nonzeroAt E (raw.relabel j) head (candidate.relabel j)
    (parameter.relabel j) hb' hn' hh ha'

theorem core (E : Program 3) (raw candidate parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) raw candidate parameter))) :
    Nonempty (Derivation body Delta (result E raw candidate parameter)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz := headTransport (PrimaryExpansion.anyEdge E) (suc z) raw z ![candidate,parameter]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A)
    have hn := InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 2)
      (PrimaryExpansion.anyStep E) z ![candidate,parameter] (constantZeroValue _)
    obtain ⟨hu⟩ := valueUnique (PrimaryExpansion.anyEdge E) (suc z) z ![z,candidate,parameter] hz hn
    exact ⟨Derivation.explosion (sucNeZeroApply hu)⟩
  · exact nonzeroCore E raw candidate parameter (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyCoreProof
