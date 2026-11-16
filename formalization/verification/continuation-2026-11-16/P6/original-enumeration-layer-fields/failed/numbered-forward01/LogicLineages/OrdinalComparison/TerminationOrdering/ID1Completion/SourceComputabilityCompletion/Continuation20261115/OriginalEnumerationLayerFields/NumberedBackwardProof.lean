module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBackwardProof
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
theorem atBranch (n : Nat) (labels heads types tupleBound prior out code range tuples : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc labels))))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples tupleBound types)))
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEncodedNumberedEnumerationBranch.branch n) out ![range,heads,types,prior,tuples,prior])))
    (hw : Nonempty (Derivation body Delta (Targets.numberedCase n labels heads types tupleBound prior code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply NumberedSyntaxProof.cases n labels heads types tupleBound prior code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph1Rename,InternalTagArithmeticSyntaxProof.sucRename] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at htj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hvec : (fun i => (![range,heads,types,prior,tuples,prior] i).relabel j) =
      ![range.relabel j,heads.relabel j,types.relabel j,prior.relabel j,tuples.relabel j,prior.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec] at hgj
  have hl := andRight (andLeft (andLeft (andLeft (andLeft hf))))
  have fields := NumberedBridgeProof.backward n (labels.relabel j) (heads.relabel j) (types.relabel j)
    (tupleBound.relabel j) (prior.relabel j) (code.relabel j) (range.relabel j) (tuples.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hrj htj hl hf
  exact OriginalEncodedNumberedEnumerationBranch.StatementChecks.exactIntroduction body beta Theta n
    (range.relabel j) (heads.relabel j) (types.relabel j) (prior.relabel j) (tuples.relabel j) (prior.relabel j)
    (out.relabel j) (code.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) hgj fields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBackwardProof
