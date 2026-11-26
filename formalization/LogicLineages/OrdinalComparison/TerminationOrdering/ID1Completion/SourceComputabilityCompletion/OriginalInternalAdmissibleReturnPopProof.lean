module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnPopProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalHereditaryReturnStepInternalSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem popCases (P : Program 1) (input rest : OTerm alpha) (psi : Formula alpha)
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.rest rest input)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (out stack : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing out (rest.relabel j) stack)) →
  Nonempty (Derivation body Theta (graph1 (OriginalHereditaryReturnStep.pop P) out (input.relabel j))) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qs : Fin 2 → Program 1 := ![consOf P OriginalHereditaryReturnStep.oldSuffix,OriginalHereditaryReturnStep.pop P]
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 apply queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hr' := renameInto hr j Theta hj
 rw [graph1Rename] at hr'
 have hp := binaryRecover InternalPairing.pairing OriginalHereditaryReturnStep.rest
   (consOf P OriginalHereditaryReturnStep.oldSuffix) (ys 1) (rest.relabel j) (ys 0) xx (hq 1) hr' (hq 0)
 exact next beta j Theta (ys 1) (ys 0) hj hp (hq 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnPopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnPopProof
