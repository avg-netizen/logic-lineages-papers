module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalParserSupportProof (selectorPair)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem stepCases (R : Program 2) (input B : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (nextState nextWork nextResults after : OTerm beta),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph1 (OriginalHereditaryCombinedStep.step R) nextState (input.relabel j))) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing nextState nextWork nextResults)) →
 Nonempty (Derivation body Theta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork (B.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let stepP : Program 2 := .composition (OriginalHereditaryCombinedStep.step R) (fun _ : Fin 1 => .projection 0)
 let qs : Fin 4 → Program 2 := ![stepP,leftOf stepP,rightOf stepP,.composition OriginalHereditaryAgendaPotential.agenda ![leftOf stepP,.projection 1] ]
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons B Fin.elim0)
 apply queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (B.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hs := unaryRecover (OriginalHereditaryCombinedStep.step R) (.projection 0) (ys 0) (input.relabel j) xx (hq 0) (projectionValue 0 xx)
 have hp := selectorPair stepP (ys 0) (ys 1) (ys 2) xx (hq 0) (hq 1) (hq 2)
 have hm := binaryRecover OriginalHereditaryAgendaPotential.agenda (leftOf stepP) (.projection 1) (ys 3) (ys 1) (B.relabel j) xx (hq 3) (hq 1) (projectionValue 1 xx)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj hs hp hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionQueryProof
