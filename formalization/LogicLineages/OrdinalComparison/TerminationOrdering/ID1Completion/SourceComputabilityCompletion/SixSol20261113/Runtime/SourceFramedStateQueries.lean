module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedStateQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem stateCases (returnFrame tagged produced suffix old : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (returnRest nextWork visitOutput results returnInput : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode returnRest (returnFrame.relabel j) (suffix.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append nextWork (tagged.relabel j) returnRest)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing visitOutput nextWork (old.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append results (produced.relabel j) (old.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing returnInput returnRest results)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let restP : Program 5 := .composition InternalListCodec.consCode ![.projection 0,.projection 3]
 let workP : Program 5 := .composition InternalApplicationValidityStackAppend.append ![.projection 1,restP]
 let visitP : Program 5 := .composition InternalPairing.pairing ![workP,.projection 4]
 let resultsP : Program 5 := .composition InternalApplicationValidityStackAppend.append ![.projection 2,.projection 4]
 let inputP : Program 5 := .composition InternalPairing.pairing ![restP,resultsP]
 let qs : Fin 5 → Program 5 := ![restP,workP,visitP,resultsP,inputP]
 let xs : Fin 5 → OTerm alpha := Fin.cons returnFrame (Fin.cons tagged (Fin.cons produced (Fin.cons suffix (Fin.cons old Fin.elim0))))
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs psi
 intro beta j Theta ys hi hq
 let xx : Fin 5 → OTerm beta := Fin.cons (returnFrame.relabel j) (Fin.cons (tagged.relabel j)
   (Fin.cons (produced.relabel j) (Fin.cons (suffix.relabel j) (Fin.cons (old.relabel j) Fin.elim0))))
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [hx] at hq
 have hr := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 3)
   (ys 0) (returnFrame.relabel j) (suffix.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 3 xx)
 have hw := binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) restP
   (ys 1) (tagged.relabel j) (ys 0) xx (hq 1) (projectionValue 1 xx) (hq 0)
 have hv := binaryRecover InternalPairing.pairing workP (.projection 4)
   (ys 2) (ys 1) (old.relabel j) xx (hq 2) (hq 1) (projectionValue 4 xx)
 have hj := binaryRecover InternalApplicationValidityStackAppend.append (.projection 2) (.projection 4)
   (ys 3) (produced.relabel j) (old.relabel j) xx (hq 3) (projectionValue 2 xx) (projectionValue 4 xx)
 have hs := binaryRecover InternalPairing.pairing restP resultsP (ys 4) (ys 0) (ys 3) xx (hq 4) (hq 0) (hq 3)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hi hr hw hv hj hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedStateQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedStateQueries
