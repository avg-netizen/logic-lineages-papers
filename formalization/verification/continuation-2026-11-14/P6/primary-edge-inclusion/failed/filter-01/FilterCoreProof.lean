module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterCoreProof
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
open Filter FilterSyntaxProof FilterBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consAt (E : Program 3) (raw head tail reached candidate parameter out rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw candidate)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)))
    (hr : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) rest tail reached parameter)))
    (hs : Nonempty (Derivation body Delta (graph4 (PrimaryExpansion.filterStep E) out head rest reached parameter))) :
    Nonempty (Derivation body Delta (result out candidate)) := by
  let A := equal head candidate
  apply formulaCases A
  · have heq : Nonempty (Derivation body (A :: Delta) (eqn candidate head)) := by
      have h : Nonempty (Derivation body (A :: Delta) (equal head candidate)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      rw [equalEqn] at h
      obtain ⟨h⟩ := h
      exact ⟨symm h⟩
    have hed : Nonempty (Derivation body (A :: Delta)
        (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached head parameter)) := by
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 (A :: Delta)
        (OrdinaryArithmetic.graphFormula (PrimaryExpansion.anyEdge E)) (suc z)
        ![reached,candidate,parameter] ![reached,head,parameter] _ (withHyp ha A)
      intro i
      simp only [InternalSourceInversionSupportProof.onEquality]
      exact Fin.cases (Nonempty.intro (refl reached))
        (Fin.cases heq (Fin.cases (Nonempty.intro (refl parameter)) (fun j => Fin.elim0 j))) i
    have hout := FilterStepProof.acceptedCons E out head rest reached parameter hed (withHyp hs A)
    exact containsHit out head rest candidate hout ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have ht := PrimaryMembership.Proof.missRecover raw head tail candidate (suc z)
      (withHyp hc A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)
    have hi := belowRawApply E raw tail reached candidate parameter rest (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not))
      (andIntro ht (andIntro (withHyp ha A.not) (withHyp hr A.not)))
    exact FilterStepProof.stepTail E out head rest reached parameter candidate (withHyp hs A.not) hi

theorem consCore (E : Program 3) (raw head tail reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw candidate)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result out candidate)) := by
  have hstep := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.filterStep E) raw head tail out ![reached,parameter] hc hf
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 2)
    (PrimaryExpansion.filterStep E) out head tail ![reached,parameter] _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hr hs
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have ha' := renameInto ha j Theta hj
  simp only [graph3Rename,sucRelabel,zRelabel] at ha'
  exact consAt E (raw.relabel j) (head.relabel j) (tail.relabel j) (reached.relabel j)
    (candidate.relabel j) (parameter.relabel j) (out.relabel j) rest hb' hc' hm' ha' hr hs

theorem nonzeroAt (E : Program 3) (raw head reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result out candidate)) := by
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
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact consCore E (raw.relabel j) (head.relabel j) tail (reached.relabel j) (candidate.relabel j)
    (parameter.relabel j) (out.relabel j) hb' (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) hm' ha' hf'

theorem nonzeroCore (E : Program 3) (raw reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result out candidate)) := by
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
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact nonzeroAt E (raw.relabel j) head (reached.relabel j) (candidate.relabel j)
    (parameter.relabel j) (out.relabel j) hb' hn' hh ha' hm' hf'

theorem core (E : Program 3) (raw reached candidate parameter out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw)))
    (ha : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.anyEdge E) (suc z) reached candidate parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw candidate)))
    (hf : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.filterReached E) out raw reached parameter))) :
    Nonempty (Derivation body Delta (result out candidate)) := by
  let A := eqn raw z
  apply formulaCases A
  · exact PrimaryExpansion.PreservationCoreProof.zeroCore raw candidate _ ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A)
  · exact nonzeroCore E raw reached candidate parameter out (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A.not) (withHyp hm A.not) (withHyp hf A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterCoreProof
