module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SupportProof

theorem nonzero2 (D : Program 2) (raw param out child head tail : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hf : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (htail : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail raw)))
    : Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  exact ConsProof.consCore D raw head tail param out child hb (reconstructNonzero raw head tail hn hhead htail) hm hf

theorem nonzero1 (D : Program 2) (raw param out child head : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hf : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    : Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  apply programCases (InternalListCodec.tailCode) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta tail hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [predecessorRename]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hnj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hfj := renameInto hf j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hheadj := renameInto hhead j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hheadj
  exact nonzero2 D (raw.relabel j) (param.relabel j) (out.relabel j) (child.relabel j) (head.relabel j) tail hbj hnj hfj hmj hheadj hx

theorem nonzero (D : Program 2) (raw param out child : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hf : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    : Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  apply programCases (InternalListCodec.headCode) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta head hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [predecessorRename]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hnj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hfj := renameInto hf j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact nonzero1 D (raw.relabel j) (param.relabel j) (out.relabel j) (child.relabel j) head hbj hnj hfj hmj hx

theorem core (D : Program 2) (raw param out child : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hf : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child))) :
    Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf0 := headTransport (ExchangeFrontier.flatten D) out raw z (Fin.cons param Fin.elim0) hz (withHyp hf A)
    have hnil : Nonempty (Derivation body (A :: Delta) (graph2 (ExchangeFrontier.flatten D) z z param)) :=
      InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) (ExchangeFrontier.flattenStep D)
        z (Fin.cons param Fin.elim0) (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))
    have he := valueUnique (ExchangeFrontier.flatten D) out z ![z,param] hf0 hnil
    have hm0 := headTransport contains (numeral 1) out z (Fin.cons child Fin.elim0) he (withHyp hm A)
    obtain ⟨bad⟩ := valueUnique contains (numeral 1) z ![z,child] hm0 (containsNil child)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · exact nonzero D raw param out child (withHyp hb A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hf A.not) (withHyp hm A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.CoreProof
