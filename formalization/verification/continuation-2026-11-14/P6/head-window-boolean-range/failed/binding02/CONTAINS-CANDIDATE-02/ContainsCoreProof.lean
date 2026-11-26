module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsCoreProof
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

open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof

theorem consRange (raw head tail needle out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains out raw needle))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  let A := equal head needle
  apply formulaCases A
  · have hh := containsHit raw head tail needle (withHyp hc A)
      (show Nonempty (Derivation body (A :: Delta) (equal head needle)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨he⟩ := valueUnique contains out (numeral 1) ![raw,needle] (withHyp hm A) hh
    exact ⟨orRight he⟩
  · have ht := PrimaryMembership.Proof.missRecover raw head tail needle out (withHyp hc A.not)
      (show Nonempty (Derivation body (A.not :: Delta) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hm A.not)
    exact atRawApply tail needle out (belowRawAt raw tail (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not))) ht

theorem nonzeroAt (raw head needle out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains out raw needle))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj ht
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at ht
  have hbj := renameInto hb j Theta hj
  rw [belowRawRename] at hbj
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  have hhj := renameInto hh j Theta hj
  rw [graph1Rename] at hhj
  have hmj := renameInto hm j Theta hj
  rw [graph2Rename] at hmj
  exact consRange (raw.relabel j) (head.relabel j) tail (needle.relabel j) (out.relabel j) hbj
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hnj hhj ht) hmj

theorem nonzeroCore (raw needle out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hm : Nonempty (Derivation body Delta (graph2 contains out raw needle))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hh
  have hbj := renameInto hb j Theta hj
  rw [belowRawRename] at hbj
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  have hmj := renameInto hm j Theta hj
  rw [graph2Rename] at hmj
  exact nonzeroAt (raw.relabel j) head (needle.relabel j) (out.relabel j) hbj hnj hh hmj

theorem core (raw needle out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains out raw needle))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf0 := headTransport contains out raw z (Fin.cons needle Fin.elim0) hz (withHyp hm A)
    obtain ⟨he⟩ := valueUnique contains out z ![z,needle] hf0 (containsNil needle)
    exact ⟨orLeft he⟩
  · exact nonzeroCore raw needle out (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsCoreProof
