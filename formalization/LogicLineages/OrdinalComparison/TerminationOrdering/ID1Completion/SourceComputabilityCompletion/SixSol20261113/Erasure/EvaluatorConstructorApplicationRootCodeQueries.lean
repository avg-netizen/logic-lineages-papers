module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationObservationQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCodeQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransport (constant)
theorem actualCases (domain codomain fnType fv av : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
  (fo ao observations typedData data candidate : OTerm beta),
  (∀ q ∈ Delta, q.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing fo (fnType.relabel j) (fv.relabel j))) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing ao (domain.relabel j) (av.relabel j))) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing observations fo ao)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typedData (codomain.relabel j) observations)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing data (domain.relabel j) typedData)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate (numeral 2) data)) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let ofn : Program 5 := pairOf (.projection 2) (.projection 3)
 let oarg : Program 5 := pairOf (.projection 0) (.projection 4)
 let obs : Program 5 := pairOf ofn oarg
 let td : Program 5 := pairOf (.projection 1) obs
 let dat : Program 5 := pairOf (.projection 0) td
 let can : Program 5 := pairOf (constant 5 2) dat
 let qs : Fin 6 → Program 5 := ![ofn,oarg,obs,td,dat,can]
 apply programsCases qs (Fin.cons domain (Fin.cons codomain (Fin.cons fnType (Fin.cons fv (Fin.cons av Fin.elim0))))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 5 → OTerm beta := Fin.cons (domain.relabel j) (Fin.cons (codomain.relabel j)
  (Fin.cons (fnType.relabel j) (Fin.cons (fv.relabel j) (Fin.cons (av.relabel j) Fin.elim0))))
 have h0 := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
  (ys 0) (fnType.relabel j) (fv.relabel j) xs (hq 0) (projectionValue 2 xs) (projectionValue 3 xs)
 have h1 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 4)
  (ys 1) (domain.relabel j) (av.relabel j) xs (hq 1) (projectionValue 0 xs) (projectionValue 4 xs)
 have h2 := binaryRecover InternalPairing.pairing ofn oarg (ys 2) (ys 0) (ys 1) xs (hq 2) (hq 0) (hq 1)
 have h3 := binaryRecover InternalPairing.pairing (.projection 1) obs (ys 3) (codomain.relabel j) (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
 have h4 := binaryRecover InternalPairing.pairing (.projection 0) td (ys 4) (domain.relabel j) (ys 3) xs (hq 4) (projectionValue 0 xs) (hq 3)
 have h5 := binaryRecover InternalPairing.pairing (constant 5 2) dat (ys 5) (numeral 2) (ys 4) xs (hq 5) (constantValue 2 xs) (hq 4)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hj h0 h1 h2 h3 h4 h5

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCodeQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCodeQueries
