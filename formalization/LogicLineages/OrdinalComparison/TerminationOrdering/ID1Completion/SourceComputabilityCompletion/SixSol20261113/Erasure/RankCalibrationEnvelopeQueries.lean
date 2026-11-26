module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Query the actual old table and actual unpair envelope of stage+1. No
semantic envelope or table-coherence premise is supplied. -/
theorem actualCases (stage : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (tab base inner root rows : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 table tab (stage.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (suc (stage.relabel j)) base inner)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing inner root rows)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let code : Program 1 := .succ
 let bas : Program 1 := leftOf code
 let inn : Program 1 := rightOf code
 let rt : Program 1 := leftOf inn
 let rw : Program 1 := rightOf inn
 let qs : Fin 5 → Program 1 := ![table,bas,inn,rt,rw]
 apply programsCases qs (Fin.cons stage Fin.elim0) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 1 → OTerm beta := Fin.cons (stage.relabel j) Fin.elim0
 have hl := unaryRecover InternalUnpair.left code (ys 1) (suc (stage.relabel j)) xs
   (hq 1) (successorValue xs)
 have hr := unaryRecover InternalUnpair.right code (ys 2) (suc (stage.relabel j)) xs
   (hq 2) (successorValue xs)
 have hrl := unaryRecover InternalUnpair.left inn (ys 3) (ys 2) xs (hq 3) (hq 2)
 have hrr := unaryRecover InternalUnpair.right inn (ys 4) (ys 2) xs (hq 4) (hq 2)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj (hq 0)
   (reconstructPair (suc (stage.relabel j)) (ys 1) (ys 2) hl hr)
   (reconstructPair (ys 2) (ys 3) (ys 4) hrl hrr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
