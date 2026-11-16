module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedForwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSyntaxProof (suc)
theorem atFields (n : Nat) (labels heads types tupleBound prior code range tuples k encoded raw t base tuple extra : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc labels))))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples tupleBound types)))
    (hf : Nonempty (Derivation body Delta (OriginalEncodedNumberedEnumerationBranch.Targets.fields n range heads types prior tuples prior code k encoded raw t base tuple extra))) :
    Nonempty (Derivation body Delta (Targets.numberedCase n labels heads types tupleBound prior code)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tuple Fin.elim0) _
  intro beta j Theta len hj hl
  simp only [consTermRename,emptyRename] at hl
  rw [NumberedSyntaxProof.caseRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph1Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at htj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [OriginalEncodedNumberedEnumerationBranch.WitnessProof.fieldsRename] at hfj
  exact NumberedSyntaxProof.introduce n (labels.relabel j) (heads.relabel j) (types.relabel j)
    (tupleBound.relabel j) (prior.relabel j) (code.relabel j)
    ![k.relabel j,encoded.relabel j,raw.relabel j,t.relabel j,base.relabel j,tuple.relabel j,extra.relabel j,len]
    (NumberedBridgeProof.forward n (labels.relabel j) (heads.relabel j) (types.relabel j)
      (tupleBound.relabel j) (prior.relabel j) (code.relabel j) (range.relabel j) (tuples.relabel j)
      (k.relabel j) (encoded.relabel j) (raw.relabel j) (t.relabel j) (base.relabel j) (tuple.relabel j) (extra.relabel j) len hrj htj hl hfj)

theorem atBranch (n : Nat) (labels heads types tupleBound prior out code range tuples : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc labels))))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples tupleBound types)))
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEncodedNumberedEnumerationBranch.branch n) out ![range,heads,types,prior,tuples,prior])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.numberedCase n labels heads types tupleBound prior code)) := by
  have hw := OriginalEncodedNumberedEnumerationBranch.StatementChecks.exactElimination body alpha Delta n
    range heads types prior tuples prior out code hg hm
  apply NumberedBridgeProof.encodedCases n range heads types prior tuples code _ hw
  intro beta j Theta ys hj hf
  rw [NumberedSyntaxProof.caseRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph1Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at htj
  exact atFields n (labels.relabel j) (heads.relabel j) (types.relabel j) (tupleBound.relabel j)
    (prior.relabel j) (code.relabel j) (range.relabel j) (tuples.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) hrj htj hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedForwardProof
