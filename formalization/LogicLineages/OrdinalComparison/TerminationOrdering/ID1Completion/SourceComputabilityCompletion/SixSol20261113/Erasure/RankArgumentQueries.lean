module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem consQueries (Q : Program 2) (typ child tail parameter : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (packed observation typed mappedTail headRank tailRank : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing packed (typ.relabel j) (child.relabel j))) →
   Nonempty (Derivation body Theta (graph2 Q observation packed (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typed (typ.relabel j) observation)) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) mappedTail (tail.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalRawSyntaxTransport.variableRankRaw headRank (child.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalRawSyntaxTransport.variableRankRaw tailRank (tail.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let packedP : Program 4 := .composition InternalPairing.pairing ![.projection 0,.projection 1]
 let observationP : Program 4 := .composition Q ![packedP,.projection 3]
 let typedP : Program 4 := .composition InternalPairing.pairing ![.projection 0,observationP]
 let mappedP : Program 4 := .composition (OriginalTypedArgumentObservations.argumentObservations Q) ![.projection 2,.projection 3]
 let headP : Program 4 := .composition OriginalRawSyntaxTransport.variableRankRaw (fun _ : Fin 1 => .projection 1)
 let tailP : Program 4 := .composition OriginalRawSyntaxTransport.variableRankRaw (fun _ : Fin 1 => .projection 2)
 let qs : Fin 6 → Program 4 := ![packedP,observationP,typedP,mappedP,headP,tailP]
 let xs : Fin 4 → OTerm alpha := ![typ,child,tail,parameter]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 4 → OTerm beta := ![typ.relabel j,child.relabel j,tail.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i
 rw [hx] at hq
 have hp := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
   (ys 0) (typ.relabel j) (child.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have ho := binaryRecover Q packedP (.projection 3) (ys 1) (ys 0) (parameter.relabel j)
   xx (hq 1) (hq 0) (projectionValue 3 xx)
 have ht := binaryRecover InternalPairing.pairing (.projection 0) observationP
   (ys 2) (typ.relabel j) (ys 1) xx (hq 2) (projectionValue 0 xx) (hq 1)
 have hm := binaryRecover (OriginalTypedArgumentObservations.argumentObservations Q) (.projection 2) (.projection 3)
   (ys 3) (tail.relabel j) (parameter.relabel j) xx (hq 3) (projectionValue 2 xx) (projectionValue 3 xx)
 have hh := unaryRecover OriginalRawSyntaxTransport.variableRankRaw (.projection 1)
   (ys 4) (child.relabel j) xx (hq 4) (projectionValue 1 xx)
 have hr := unaryRecover OriginalRawSyntaxTransport.variableRankRaw (.projection 2)
   (ys 5) (tail.relabel j) xx (hq 5) (projectionValue 2 xx)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hj hp ho ht hm hh hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentQueries
