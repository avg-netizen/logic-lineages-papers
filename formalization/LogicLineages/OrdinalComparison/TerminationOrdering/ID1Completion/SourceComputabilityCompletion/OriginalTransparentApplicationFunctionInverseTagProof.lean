module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInversePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationValidityClosure (applicationConstructors)
open OriginalTransparentApplicationFunctionDefinitions
open OriginalTransparentMixedPathInternalDefinitions (ApplicationHop)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem sourceTag (S : Program 2) (s t cert parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (graph4 (hopGuard S) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag positionTerm s)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 apply programCases edge xs _
 intro beta j Theta state hj hedge
 simp only [xs,consTermRename,emptyRename] at hedge
 let xx : Fin 4 → OTerm beta := Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
   (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
 have hg' := renameInto hg j Theta hj
 simp only [graph4Rename,sucRelabel,zRelabel] at hg'
 rw [graph1Rename,InternalApplicationCertificateConstructorsSyntaxProof.positionTermRename]
 have hparts := conjunctionRecover (OriginalTransparentVariableStep.sourceAt S) structuralGuard xx hg'
 have hstruct := unaryRecover InternalApplicationStepPeel.structuralGuard edge (suc z) state xx (andRight hparts) hedge
 have hedge3 : Nonempty (Derivation body Theta (graph3 edgeCode state (s.relabel j) (t.relabel j) (cert.relabel j))) := by
   apply compositionRecover edgeCode ![.projection 0,.projection 1,.projection 2] state xx
     (Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons (cert.relabel j) Fin.elim0))) hedge
   intro i
   exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
     (Fin.cases (projectionValue 2 xx) (fun k => Fin.elim0 k))) i
 have hparts' := OriginalTransparentApplicationFunctionInverseSupportProof.guardParts state hstruct
 have htag := OriginalTransparentApplicationFunctionInverseSupportProof.sameLeft
   (InternalApplicationStepPeel.constructorTag InternalApplicationCertificateConstructors.source)
   (two 1) positionTerm (Fin.cons state Fin.elim0)
   (andLeft (andRight (andRight hparts'))) (twoValue _)
 exact OriginalTransparentApplicationFunctionInverseGeometryProof.tagAtInput
   InternalApplicationCertificateConstructors.source state (s.relabel j)
   (andLeft (edgeSelectors state (s.relabel j) (t.relabel j) (cert.relabel j) hedge3)) htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTagProof
