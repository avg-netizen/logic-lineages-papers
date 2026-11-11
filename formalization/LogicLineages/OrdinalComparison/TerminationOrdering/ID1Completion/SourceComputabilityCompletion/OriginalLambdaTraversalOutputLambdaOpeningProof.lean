module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversal OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Bind only literal raw lambda selectors and the actual child parameter.
No accepted-source or native wellformedness premise is needed for this query. -/
theorem lambdaFieldsCases (input parameter : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag InternalOriginalStepGuard.one input)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (d e child bodyParameter : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (LambdaFields (input.relabel j) d e child (parameter.relabel j) bodyParameter)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let domainP : Program 2 := .composition rawDomain (fun _ : Fin 1 => .projection 0)
  let codomainP : Program 2 := .composition rawCodomain (fun _ : Fin 1 => .projection 0)
  let bodyP : Program 2 := .composition rawBody (fun _ : Fin 1 => .projection 0)
  let qs : Fin 4 → Program 2 := ![domainP,codomainP,bodyP,childParameter]
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply InternalApplicationStepPeelSupportProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ht'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hd := unaryRecover rawDomain (.projection 0) (ys 0) (input.relabel j) xx (hq 0) (projectionValue 0 xx)
  have he := unaryRecover rawCodomain (.projection 0) (ys 1) (input.relabel j) xx (hq 1) (projectionValue 0 xx)
  have hb := unaryRecover rawBody (.projection 0) (ys 2) (input.relabel j) xx (hq 2) (projectionValue 0 xx)
  exact k beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj
    (andIntro ht' (andIntro hd (andIntro he (andIntro hb (hq 3)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
