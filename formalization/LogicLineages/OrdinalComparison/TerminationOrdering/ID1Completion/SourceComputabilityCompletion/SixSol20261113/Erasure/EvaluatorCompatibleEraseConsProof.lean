module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleEraseConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open EvaluatorErasureDefinitions EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual zero-cutoff erasure of an admitted pair in a cons context. All
in-range, lookup, delete and length facts are derived, not supplied. -/
theorem actualAtCons (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right erasedLeft erasedRight d gamma extended c parameter erasedParameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c extended)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParameter c gamma)))
 (hl : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d z left)))
 (hr : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d z right))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W erasedLeft erasedRight erasedParameter)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons gamma Fin.elim0) _
 intro beta j Theta count hj hlength
 rw [admittedRename]
 simp only [consTermRename,emptyRename] at hlength
 have ha' := renameInto ha j Theta hj
 have hc' := renameInto hc j Theta hj
 have hp' := renameInto hp j Theta hj
 have hn' := renameInto hn j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [admittedRename] at ha'
 simp only [graph2Rename,graph3Rename,zRelabel] at hc' hp' hn' hl' hr'
 have hext := OriginalContextInsertionLengthProof.lengthCons (extended.relabel j) (d.relabel j) (gamma.relabel j) count hc' hlength
 have hk := OriginalAllPositionContextDeleteBaseProof.lookupZero (extended.relabel j) (d.relabel j) (gamma.relabel j) hc'
 have hd := OriginalAllPositionContextDeleteBaseProof.deleteZero (extended.relabel j) (d.relabel j) (gamma.relabel j) hc'
 have hb : Nonempty (Derivation body Theta (OriginalContextInsertion.Below z (suc count))) :=
   ⟨InternalQuotientComparisonProof.zeroLessSuccessor count⟩
 exact EvaluatorErasureProof.actualErasureCongruence R H G M W body beta Theta
   (left.relabel j) (right.relabel j) (erasedLeft.relabel j) (erasedRight.relabel j)
   (parameter.relabel j) (erasedParameter.relabel j) (c.relabel j) (extended.relabel j) (gamma.relabel j)
   (suc count) z (d.relabel j) ha' hp' hn' hext hb hk hd hl' hr'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleEraseConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleEraseConsProof
