module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
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

/-- A recognized front cell descends at the four ACTUAL child selectors,
including its actual runtime child parameter. No context covariance assumed. -/
theorem knownChild (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail childS childT childCert childParam : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceBody childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.targetBody childT s t cert parameter)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert parameter)))
 (hm : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter childParam s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph1 InternalUnpair.left tail childCert ⊓
   graph4 (recognizes source leaf) (suc z) childS childT childCert childParam)) := by
 apply OriginalLambdaDirectBottomTraceFrontQueryProof.frontCases source leaf s t cert parameter code head tail _ hp hc ha
 intro beta rho Theta next out hrho hhop hl hr hf
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have hk' := renameInto hk rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 simp only [graph1Rename] at hp'
 simp only [graph2Rename] at hc'
 simp only [graph4Rename] at hs' ht' hk' hm'
 simp only [conjunctionRename,graph1Rename,graph4Rename,sucRelabel,zRelabel]
 let xs : Fin 4 → OTerm beta := ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
 let ys : Fin 4 → OTerm beta := ![childS.relabel rho,childT.relabel rho,childCert.relabel rho,childParam.relabel rho]
 have hh : ∀ i : Fin 4, Nonempty (Derivation body Theta
   (programGraph ((![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
     OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] : Fin 4 → Program 4) i) (ys i) xs)) := by
  intro i
  exact Fin.cases hs' (Fin.cases ht' (Fin.cases hk' (Fin.cases hm' (fun j => Fin.elim0 j)))) i
 have hv := compositionRecover OriginalHereditaryLambda.live
  (![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
    OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] : Fin 4 → Program 4)
  next xs ys hl hh
 have hpath := unaryValue InternalUnpair.left (.projection 2) (code.relabel rho) (cert.relabel rho) xs hp'
   (projectionValue (2 : Fin 4) xs)
 have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction
   (code.relabel rho) (head.relabel rho) (tail.relabel rho) hc'))
 exact OriginalLambdaDirectBottomTraceChildRunProof.actualChildRun source leaf body beta Theta
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
   (code.relabel rho) (tail.relabel rho) (childS.relabel rho) (childT.relabel rho)
   (childCert.relabel rho) (childParam.relabel rho) next out hpath htail hk' hv hr hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
