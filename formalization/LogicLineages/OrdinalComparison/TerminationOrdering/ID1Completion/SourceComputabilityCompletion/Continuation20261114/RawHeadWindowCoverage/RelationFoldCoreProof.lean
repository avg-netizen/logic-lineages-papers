module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RelationFold RelationFoldSyntaxProof RelationFoldBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

variable {k : Nat}
def Hit (body : Positive (Fin 1)) (step : Program (k+2)) (transform : Program (k+2)) : Prop :=
  ∀ (alpha : Type) (Delta : List (Formula alpha)) (head rest out image : OTerm alpha) (params : Fin k → OTerm alpha),
    Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons head params)))) →
    Nonempty (Derivation body Delta (programGraph step out (Fin.cons head (Fin.cons rest params)))) →
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image))
def Tail (body : Positive (Fin 1)) (step : Program (k+2)) : Prop :=
  ∀ (alpha : Type) (Delta : List (Formula alpha)) (head rest out image : OTerm alpha) (params : Fin k → OTerm alpha),
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) rest image)) →
    Nonempty (Derivation body Delta (programGraph step out (Fin.cons head (Fin.cons rest params)))) →
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image))
variable (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
variable (hit : Hit body step transform) (keep : Tail body step)

theorem consAt (raw head tail needle image out rest : OTerm alpha) (params : Fin k → OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) rest (Fin.cons tail params))))
    (ht : Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hs : Nonempty (Derivation body Delta (programGraph step out (Fin.cons head (Fin.cons rest params))))) :
    Nonempty (Derivation body Delta (result out image)) := by
  let A := equal head needle
  apply formulaCases A
  · have he : Nonempty (Derivation body (A :: Delta) (eqn needle head)) := by
      have h : Nonempty (Derivation body (A :: Delta) (equal head needle)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      rw [equalEqn] at h
      obtain ⟨h⟩ := h
      exact ⟨symm h⟩
    have ht' := withHyp ht A
    have moved : Nonempty (Derivation body (A :: Delta)
        (programGraph transform (numeral 1) (Fin.cons image (Fin.cons head params)))) := by
      unfold programGraph at ht' ⊢
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha (k+2) (A :: Delta)
        (OrdinaryArithmetic.graphFormula transform) (numeral 1)
        (Fin.cons image (Fin.cons needle params)) (Fin.cons image (Fin.cons head params)) _ ht'
      intro i
      simp only [InternalSourceInversionSupportProof.onEquality]
      exact Fin.cases (Nonempty.intro (InternalTagArithmeticSupportProof.refl image))
        (Fin.cases he (fun i => Nonempty.intro (InternalTagArithmeticSupportProof.refl (params i)))) i
    exact hit alpha (A :: Delta) head rest out image params moved (withHyp hs A)
  · have hmem := PrimaryMembership.Proof.missRecover raw head tail needle (numeral 1)
      (withHyp hc A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)
    have ih := belowRawApply base step transform raw tail needle image rest params (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not))
      (andIntro (withHyp hr A.not) (andIntro (withHyp ht A.not) hmem))
    exact keep alpha (A.not :: Delta) head rest out image params ih (withHyp hs A.not)

theorem consCore (raw head tail needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hf : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params)))) :
    Nonempty (Derivation body Delta (result out image)) := by
  have hstep := InternalRawListRecursionProof.consForward base step raw head tail out params hc hf
  apply InternalRawListRecursionProof.stepCases base step out head tail params _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ht' := renameInto ht j Theta hj
  simp only [programRename,consTermRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hr' : Nonempty (Derivation body Theta (programGraph (InternalRawListRecursion.listRec base step)
      rest (Fin.cons (tail.relabel j) (fun i => (params i).relabel j)))) := by
    simpa only [programGraph,InternalRawListRecursion.recGraph] using hr
  exact consAt base step transform hit keep (raw.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (image.relabel j) (out.relabel j) rest (fun i => (params i).relabel j) hb' hc' hr' ht' hm' hs

theorem nonzeroAt (raw head needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (ht : Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hf : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params)))) :
    Nonempty (Derivation body Delta (result out image)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj hv
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hv
  have hb' := renameInto hb j Theta hj
  simp only [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  simp only [nonzeroRename] at hn'
  have hh' := renameInto hh j Theta hj
  simp only [graph1Rename] at hh'
  have ht' := renameInto ht j Theta hj
  simp only [programRename,consTermRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hf' := renameInto hf j Theta hj
  simp only [programRename,consTermRename,GuardedSourceSyntaxProof.numeralRename] at hf'
  exact consCore base step transform hit keep (raw.relabel j) (head.relabel j) tail (needle.relabel j) (image.relabel j) (out.relabel j) (fun i => (params i).relabel j) hb'
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' hv) ht' hm' hf'

theorem nonzeroCore (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (ht : Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hf : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params)))) :
    Nonempty (Derivation body Delta (result out image)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hv
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hv
  have hb' := renameInto hb j Theta hj
  simp only [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  simp only [nonzeroRename] at hn'
  have ht' := renameInto ht j Theta hj
  simp only [programRename,consTermRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hf' := renameInto hf j Theta hj
  simp only [programRename,consTermRename,GuardedSourceSyntaxProof.numeralRename] at hf'
  exact nonzeroAt base step transform hit keep (raw.relabel j) head (needle.relabel j) (image.relabel j) (out.relabel j) (fun i => (params i).relabel j) hb' hn' hv ht' hm' hf'

theorem core (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw)))
    (ht : Nonempty (Derivation body Delta (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hf : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params)))) :
    Nonempty (Derivation body Delta (result out image)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz := headTransport contains (numeral 1) raw z (Fin.cons needle Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A)
    obtain ⟨hbad⟩ := valueUnique contains (numeral 1) z ![z,needle] hz (containsNil needle)
    exact ⟨Derivation.explosion (sucNeZeroApply hbad)⟩
  · exact nonzeroCore base step transform hit keep raw needle image out params (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht A.not) (withHyp hm A.not) (withHyp hf A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFoldCoreProof
