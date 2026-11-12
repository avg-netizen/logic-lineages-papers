module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Query actual head metadata, all of its arrow fields, raw payload and list annotation.
Even zero metadata is queried; its rejection is paid by decoder acceptance. -/
theorem metadataCases (H : Program 1) (head raw : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
 (data result types payload annotation : OTerm beta),
 (∀ p ∈ Delta, p.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph1 H data (head.relabel j))) →
 Nonempty (Derivation body Theta (StepArrowFields data result types)) →
 Nonempty (Derivation body Theta (graph1 InternalUnpair.right payload (raw.relabel j))) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing annotation (numeral 1) (numeral 0))) →
 Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let h : Program 2 := .composition H (fun _ : Fin 1 => .projection 0)
 let a : Program 2 := pairOf (constant 2 1) (constant 2 0)
 let qs : Fin 5 → Program 2 := ![h,OriginalTypedDecoder.headOf h,OriginalTypedDecoder.tailOf h,rightOf (.projection 1),a]
 let xs : Fin 2 → OTerm alpha := ![head,raw]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs psi
 intro beta j Theta ys hj hq
 let xx : Fin 2 → OTerm beta := ![head.relabel j,raw.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj
  (unaryRecover H (.projection 0) (ys 0) (head.relabel j) xx (hq 0) (projectionValue 0 xx))
  (OriginalTypedDecoderInternalScalarProof.arrowFields h (ys 0) (ys 1) (ys 2) xx (hq 0) (hq 1) (hq 2))
  (unaryRecover InternalUnpair.right (.projection 1) (ys 3) (raw.relabel j) xx (hq 3) (projectionValue 1 xx))
  (binaryRecover InternalPairing.pairing (constant 2 1) (constant 2 0) (ys 4) (numeral 1) (numeral 0) xx
   (hq 4) (constantValue 1 xx) (constantValue 0 xx))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildQueriesProof
