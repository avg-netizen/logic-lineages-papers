module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalPreservationInductionDefinitions
open EvaluatorKeyCanonicalInductionDefinitions (C)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open EvaluatorKeyCanonicalPreservationSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
theorem withOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W)
 (q input out parameter arrow d e fp ap fn arg : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
 (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
 (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 let cf : Program 3 := .composition (C p H G W P) ![.projection 0,.projection 2]
 let ca : Program 3 := .composition (C p H G W P) ![.projection 1,.projection 2]
 let rf : Program 3 := rightOf cf
 let ra : Program 3 := rightOf ca
 apply programsCases (![cf,ca,rf,ra] : Fin 4 → Program 3)
  (Fin.cons fn (Fin.cons arg (Fin.cons parameter Fin.elim0))) _
 intro beta j Theta ys hj hq
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 3 → OTerm beta := Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
 have hf := binaryRecover (C p H G W P) (.projection 0) (.projection 2)
  (ys 0) (fn.relabel j) (parameter.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 2 xs)
 have ha := binaryRecover (C p H G W P) (.projection 1) (.projection 2)
  (ys 1) (arg.relabel j) (parameter.relabel j) xs (hq 1) (projectionValue 1 xs) (projectionValue 2 xs)
 have hfr := unaryRecover InternalUnpair.right cf (ys 2) (ys 0) xs (hq 2) (hq 0)
 have har := unaryRecover InternalUnpair.right ca (ys 3) (ys 1) xs (hq 3) (hq 1)
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hc' := renameInto hc j Theta hj
 have hfl' := renameInto hfl j Theta hj
 have hal' := renameInto hal j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 simp only [applicationConstructors,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,graph4Rename] at hc'
 simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
 exact EvaluatorKeyCanonicalPreservationApplicationSemanticProof.atOutputs p H G W P compat
  (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j)
  (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j)
  (ys 0) (ys 1) (ys 2) (ys 3) hb' hp' hc' hfl' hal' hf ha hfr har
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationQueriesProof
