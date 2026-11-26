module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawSyntaxTransportInternalParametersQueryProof

/-- Six internal queries pay both transformed children and their before/after
ranks at once. No successful child computation is assumed in the caller. -/
theorem binaryTransportCases (p : Program 3) (r : Program 1)
    (d k first second : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p firstOut (d.relabel j) (k.relabel j) (first.relabel j))) →
      Nonempty (Derivation body Theta (graph3 p secondOut (d.relabel j) (k.relabel j) (second.relabel j))) →
      Nonempty (Derivation body Theta (graph1 r beforeFirst (first.relabel j))) →
      Nonempty (Derivation body Theta (graph1 r beforeSecond (second.relabel j))) →
      Nonempty (Derivation body Theta (graph1 r afterFirst firstOut)) →
      Nonempty (Derivation body Theta (graph1 r afterSecond secondOut)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qFirst : Program 4 := .composition p ![.projection 0,.projection 1,.projection 2]
  let qSecond : Program 4 := .composition p ![.projection 0,.projection 1,.projection 3]
  let qs : Fin 6 → Program 4 := ![qFirst,qSecond,
    .composition r (fun _ : Fin 1 => .projection 2),
    .composition r (fun _ : Fin 1 => .projection 3),
    .composition r (fun _ : Fin 1 => qFirst),
    .composition r (fun _ : Fin 1 => qSecond)]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons first (Fin.cons second Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  let xs' : Fin 4 → OTerm beta := fun i => (xs i).relabel j
  exact step beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hj
    (projectionTripleRecover p 0 1 2 (ys 0) xs' (hq 0))
    (projectionTripleRecover p 0 1 3 (ys 1) xs' (hq 1))
    (unaryRecover r (.projection 2) (ys 2) (first.relabel j) xs' (hq 2) (projectionValue 2 xs'))
    (unaryRecover r (.projection 3) (ys 3) (second.relabel j) xs' (hq 3) (projectionValue 3 xs'))
    (unaryRecover r qFirst (ys 4) (ys 0) xs' (hq 4) (hq 0))
    (unaryRecover r qSecond (ys 5) (ys 1) xs' (hq 5) (hq 1))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportQueryProof
