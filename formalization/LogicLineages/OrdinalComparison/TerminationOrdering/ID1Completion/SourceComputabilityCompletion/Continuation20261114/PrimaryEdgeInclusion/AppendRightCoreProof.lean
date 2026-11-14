module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightCoreProof
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
open InternalApplicationValidityStackAppend (append)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open AppendRight AppendRightSyntaxProof AppendRightBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCore (raw suffix out needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw z)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
  have hz := headTransport append out raw z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hu⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover out suffix hz
  exact headTransport contains (suc z) suffix out (Fin.cons needle Fin.elim0) ⟨symm hu⟩ hm

theorem consAt (raw head tail suffix out rest needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 append rest tail suffix)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
  have hi := belowRawApply raw tail suffix rest needle hb
    (consTailDescent raw head tail hc) (andIntro hr hm)
  let A := equal head needle
  apply formulaCases A
  · exact containsHit out head rest needle (withHyp ho A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact containsMiss out head rest needle (suc z) (withHyp ho A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hi A.not)

theorem consCore (raw head tail suffix out needle : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
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
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
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
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
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
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) suffix needle))) :
    Nonempty (Derivation body Delta (result out needle)) := by
  let A := eqn raw z
  apply formulaCases A
  · exact zeroCore raw suffix out needle ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ha A) (withHyp hm A)
  · exact nonzeroCore raw suffix out needle (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A.not) (withHyp hm A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightCoreProof
