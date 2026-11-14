module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalPositiveUnfoldingSupportProof InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationValidityStackAppend (append)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Append AppendSyntaxProof AppendBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCore (raw suffix out needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw z)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
  have hz := headTransport append out raw z (Fin.cons suffix Fin.elim0) he ha
  have hu := InternalApplicationValidityStackAppendListProof.appendZeroRecover out suffix hz
  obtain ⟨h⟩ := headTransport contains (suc z) out suffix (Fin.cons needle Fin.elim0) hu hm
  exact ⟨orRight h⟩

theorem consAt (raw head tail suffix out rest needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 append rest tail suffix)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
  let A := equal head needle
  apply formulaCases A
  · obtain ⟨h⟩ := containsHit raw head tail needle (withHyp hc A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨orLeft h⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover out head rest needle (suc z)
      (withHyp ho A.not) hn (withHyp hm A.not)
    obtain ⟨hi⟩ := belowRawApply raw tail suffix rest needle (withHyp hb A.not)
      (consTailDescent raw head tail (withHyp hc A.not)) (andIntro (withHyp hr A.not) ht)
    let L := graph2 contains (suc z) tail needle
    let R := graph2 contains (suc z) suffix needle
    obtain ⟨hl⟩ := containsMiss raw head tail needle (suc z)
      (withHyp (withHyp hc A.not) L) (withHyp hn L) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨disjunctionElimination hi
      (Derivation.implicationIntroduction (orLeft hl))
      (Derivation.implicationIntroduction (orRight (Derivation.hypothesis List.mem_cons_self)))⟩

theorem consCore (raw head tail suffix out needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
  apply programCases append (Fin.cons tail (Fin.cons suffix Fin.elim0)) _
  intro beta j Theta rest hj hr
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hr
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have ho := InternalApplicationValidityStackAppendListProof.consForward
    (raw.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j)
    rest (out.relabel j) hc' hr ha'
  exact consAt (raw.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j)
    (out.relabel j) rest (needle.relabel j) hb' hc' hr ho hm'

theorem nonzeroAt (raw head suffix out needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
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
  rw [graph2Rename] at ha'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  exact consCore (raw.relabel j) (head.relabel j) tail (suffix.relabel j) (out.relabel j)
    (needle.relabel j) hb' (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) ha' hm'

theorem nonzeroCore (raw suffix out needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hh
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [nonzeroRename] at hn'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  exact nonzeroAt (raw.relabel j) head (suffix.relabel j) (out.relabel j)
    (needle.relabel j) hb' hn' hh ha' hm'

theorem core (raw suffix out needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) := by
  let A := eqn raw z
  apply formulaCases A
  · exact zeroCore raw suffix out needle ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ha A) (withHyp hm A)
  · exact nonzeroCore raw suffix out needle (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A.not) (withHyp hm A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendCoreProof
