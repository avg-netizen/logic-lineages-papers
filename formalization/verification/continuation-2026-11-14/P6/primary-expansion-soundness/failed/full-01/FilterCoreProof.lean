module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
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
open Filter FilterSyntaxProof FilterBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem liftResult (E : Program 3) (raw head tail reached candidate parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (result E tail reached candidate parameter))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  obtain ⟨hi⟩ := hi
  exact andIntro (PrimaryEdgeInclusion.FilterStepProof.consContainsTail raw head tail candidate hc
    ⟨Derivation.conjunctionLeft hi⟩) ⟨Derivation.conjunctionRight hi⟩

theorem acceptedCase (E : Program 3) (raw head tail reached candidate parameter out rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) rest tail reached parameter)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached head parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  let A := equal head candidate
  apply formulaCases A
  · have heq : Nonempty (Derivation body (A :: Delta) (eqn head candidate)) := by
      have h : Nonempty (Derivation body (A :: Delta) (equal head candidate)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      simpa only [equalEqn] using h
    have ha' := withHyp ha A
    have hedge : Nonempty (Derivation body (A :: Delta)
        (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)) := by
      unfold graph3 programGraph at ha' ⊢
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 (A :: Delta)
        (OrdinaryArithmetic.graphFormula (PrimaryExpansion.anyEdge E)) (suc z)
        ![reached,head,parameter] ![reached,candidate,parameter] _ ha'
      intro i
      simp only [InternalSourceInversionSupportProof.onEquality]
      exact Fin.cases (Nonempty.intro (refl reached))
        (Fin.cases heq (Fin.cases (Nonempty.intro (refl parameter)) (fun j => Fin.elim0 j))) i
    exact andIntro (containsHit raw head tail candidate (withHyp hc A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩) hedge
  · have ht := PrimaryMembership.Proof.missRecover out head rest candidate (suc z)
      (withHyp ho A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)
    have hi := belowRawApply E raw tail reached candidate parameter rest (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not)) (andIntro (withHyp hr A.not) ht)
    exact liftResult E raw head tail reached candidate parameter (withHyp hc A.not) hi

theorem consAt (E : Program 3) (raw head tail reached candidate parameter out rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) rest tail reached parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 (PrimaryExpansion.filterStep E) out head rest reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,reached,parameter]
  let query : Program 4 := .composition (PrimaryExpansion.anyEdge E) ![.projection 2,.projection 0,.projection 3]
  let A := programGraph query (suc z) xs
  apply formulaCases A
  · have ha : Nonempty (Derivation body (A :: Delta)
        (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached head parameter)) := by
      apply compositionRecover (PrimaryExpansion.anyEdge E) ![.projection 2,.projection 0,.projection 3]
        (suc z) xs ![reached,head,parameter] ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro i
      exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 0 xs)
        (Fin.cases (projectionValue 3 xs) (fun j => Fin.elim0 j))) i
    have ho := PrimaryEdgeInclusion.FilterStepProof.acceptedCons E out head rest reached parameter ha (withHyp hs A)
    exact acceptedCase E raw head tail reached candidate parameter out rest
      (withHyp hb A) (withHyp hc A) (withHyp hr A) ho ha (withHyp hm A)
  · have hp := zeroBranchElim (normalize query) (.projection 1)
      (.composition InternalListCodec.consCode ![.projection 0,.projection 1]) out xs
      (normalizeReject query xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hs A.not)
    have hu := valueUnique (.projection (1 : Fin 4)) out rest xs hp (projectionValue 1 xs)
    have ht := headTransport contains (suc z) out rest (Fin.cons candidate Fin.elim0) hu (withHyp hm A.not)
    have hi := belowRawApply E raw tail reached candidate parameter rest (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not)) (andIntro (withHyp hr A.not) ht)
    exact liftResult E raw head tail reached candidate parameter (withHyp hc A.not) hi

theorem consCore (E : Program 3) (raw head tail reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  have hstep := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.filterStep E) raw head tail out ![reached,parameter] hc hf
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.filterStep E) out head tail ![reached,parameter] _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have hparams : (fun i => (![reached,parameter] i).relabel j) =
      Fin.cons (reached.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hparams] at hr hs
  have hr' : Nonempty (Derivation body Theta
      (graph3 (PrimaryExpansion.filterReached E) rest (tail.relabel j)
        (reached.relabel j) (parameter.relabel j))) := by
    simpa only [graph3,programGraph,PrimaryExpansion.filterReached,InternalRawListRecursion.recGraph] using hr
  exact consAt E (raw.relabel j) (head.relabel j) (tail.relabel j) (reached.relabel j)
    (candidate.relabel j) (parameter.relabel j) (out.relabel j) rest hb' hc' hr' hs hm'

theorem nonzeroAt (E : Program 3) (raw head reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
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
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact consCore E (raw.relabel j) (head.relabel j) tail (reached.relabel j) (candidate.relabel j)
    (parameter.relabel j) (out.relabel j) hb' (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) hm' hf'

theorem nonzeroCore (E : Program 3) (raw reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hh
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [nonzeroRename] at hn'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact nonzeroAt E (raw.relabel j) head (reached.relabel j) (candidate.relabel j)
    (parameter.relabel j) (out.relabel j) hb' hn' hh hm' hf'

theorem core (E : Program 3) (raw reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result E raw reached candidate parameter)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz := headTransport (PrimaryExpansion.filterReached E) out raw z ![reached,parameter]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf A)
    have hn := InternalRawListRecursionProof.nilValue (body := body) (Gamma := A :: Delta) (InternalAcceptance.constantZero 2)
      (PrimaryExpansion.filterStep E) z ![reached,parameter] (constantZeroValue _)
    have hu := valueUnique (PrimaryExpansion.filterReached E) out z ![z,reached,parameter] hz hn
    have hnil := headTransport contains (suc z) out z (Fin.cons candidate Fin.elim0) hu (withHyp hm A)
    obtain ⟨hbad⟩ := valueUnique contains (suc z) z ![z,candidate] hnil (containsNil candidate)
    exact ⟨Derivation.explosion (sucNeZeroApply hbad)⟩
  · exact nonzeroCore E raw reached candidate parameter out (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not) (withHyp hf A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
