module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransportInternalParserSupportProof (selectorPair)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalInternalRawSameContextSupportProof OriginalInternalRawSameContextWindowProof

theorem actualCases : OriginalInternalRawSameContextTargets.ActualCases := by
 intro body alpha Delta raw parameter window gamma jobs count index child psi hp he hl hb hv next
 have hw := rawWindow raw parameter window gamma jobs count index child hp he hl hb hv
 let qs : Fin 3 → Program 1 := ![leftOf (.projection 0),rightOf (.projection 0),rightOf (rightOf (.projection 0))]
 let xs : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 1 → OTerm beta := Fin.cons (child.relabel rho) Fin.elim0
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hw' := renameInto hw rho Theta hrho
 rw [graph1Rename] at hw'
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) hrho
   (selectorPair (.projection 0) (child.relabel rho) (ys 0) (ys 1) xx (projectionValue 0 xx) (hq 0) (hq 1))
   (selectorPair (rightOf (.projection 0)) (ys 1) (window.relabel rho) (ys 2) xx (hq 1) hw' (hq 2))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextProof
