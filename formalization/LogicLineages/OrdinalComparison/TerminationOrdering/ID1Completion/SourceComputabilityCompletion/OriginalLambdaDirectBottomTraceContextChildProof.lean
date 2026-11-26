module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceContextChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalLambdaDirectBottomTraceInductionDefinitions
/-- Context-aware child induction: every retained parent hypothesis is
explicitly transported into the caller's arithmetic context. -/
theorem atChild (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail oldBody domain codomain arrow d cutoff c : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf code)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (hfields : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow)))
 (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
 (incl : ∀ f ∈ Delta, f.relabel j ∈ Theta)
 (oldChildS oldChildT oldCert oldParam childS childT childParam gamma extended : OTerm beta)
 (hbs : Nonempty (Derivation body Theta (graph2 OriginalLambdaConstructor.bodyCode oldChildS (codomain.relabel j) (s.relabel j))))
 (hbt : Nonempty (Derivation body Theta (graph2 OriginalLambdaConstructor.bodyCode oldChildT (codomain.relabel j) (t.relabel j))))
 (hs : Nonempty (Derivation body Theta (graph2 source (suc z) oldChildS oldParam)))
 (hl : Nonempty (Derivation body Theta (graph4 leaf (suc z) oldChildS oldChildT oldCert oldParam)))
 (hop : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing oldParam (c.relabel j) extended)))
 (hnp : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParam (c.relabel j) gamma)))
 (hin : Nonempty (Derivation body Theta (OriginalContextInsertion.Insert (d.relabel j) (suc (cutoff.relabel j)) gamma extended)))
 (hes : Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childS (d.relabel j) (suc (cutoff.relabel j)) oldChildS)))
 (het : Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childT (d.relabel j) (suc (cutoff.relabel j)) oldChildT)))
 (hstrip : Nonempty (Derivation body Theta (graph1 OriginalLambdaGuardLeaf.stripCertificate oldCert (cert.relabel j))))
 (hparam : Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.childParameter oldParam (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)))) :
 Nonempty (Derivation body Theta (OriginalLambdaOriginalRankDefinitions.Result leaf childS childT childParam oldChildS oldChildT
   ((SourceComputabilityFormulaSupportProof.numeral 1).relabel j) ((SourceComputabilityFormulaSupportProof.numeral 0).relabel j))) := by
 have hi' := renameInto hi j Theta incl
 have hp' := renameInto hp j Theta incl
 have hc' := renameInto hc j Theta incl
 have ha' := renameInto ha j Theta incl
 have hf' := renameInto hfields j Theta incl
 simp only [OriginalLambdaDirectBottomTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph1Rename] at hp'
 simp only [graph2Rename] at hc'
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 simp only [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hf'
 have hb := OriginalLambdaDirectBottomTraceBodySelectorsProof.bodySelectors
   (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
   (oldBody.relabel j) oldChildS oldChildT (domain.relabel j) (codomain.relabel j) (arrow.relabel j) hf' hbs hbt
 let xs : Fin 4 → OTerm beta := ![s.relabel j,t.relabel j,cert.relabel j,parameter.relabel j]
 have hk := unaryValue OriginalLambdaGuardLeaf.stripCertificate (.projection 2) oldCert (cert.relabel j) xs
   hstrip (projectionValue (2 : Fin 4) xs)
 have hr := OriginalLambdaDirectBottomTraceChildInductionProof.childResult source leaf
   (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
   (code.relabel j) (head.relabel j) (tail.relabel j) oldChildS oldChildT oldCert oldParam
   childParam gamma extended (d.relabel j) (suc (cutoff.relabel j)) (c.relabel j) childS childT
   hi' hp' hc' ha' (andLeft hb) (andRight hb) hk hparam hs hl hin hop hnp hes het
 simpa only [GuardedSourceSyntaxProof.numeralRename] using andRight hr

theorem contextIH (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail oldBody domain codomain arrow d cutoff c : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf code)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow))) :
 OriginalLambdaErasureContextCaseDefinitions.ContextChildIH body Delta leaf source
  s t cert parameter codomain d cutoff c (SourceComputabilityFormulaSupportProof.numeral 1)
  (SourceComputabilityFormulaSupportProof.numeral 0) := by
 intro beta j Theta incl oldChildS oldChildT oldCert oldParam childS childT childParam gamma extended
   hbs hbt hs hl hop hnp hin hes het hstrip hparam
 exact atChild source leaf s t cert parameter code head tail oldBody domain codomain arrow d cutoff c
   hi hp hc ha hf beta j Theta incl oldChildS oldChildT oldCert oldParam childS childT childParam gamma extended
   hbs hbt hs hl hop hnp hin hes het hstrip hparam

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceContextChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceContextChildProof
