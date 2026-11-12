module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalListCodecSupportProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryDeletionRows
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanCases (Q : Program 2) (count input parameter : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (previous value singleton : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph3 (scan Q) previous (count.relabel j) (input.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 (observation Q) value (count.relabel j) (input.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Theta (consGraph singleton value z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let single : Program 3 := .composition InternalListCodec.consCode
    ![observation Q,InternalAcceptance.constantZero 3]
  let qs : Fin 3 → Program 3 := ![scan Q,observation Q,single]
  let xs : Fin 3 → OTerm alpha := Fin.cons count (Fin.cons input (Fin.cons parameter Fin.elim0))
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm beta := Fin.cons (count.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have hz := InternalRawListRecursionSupportProof.constantZero (body := body) (Gamma := Theta) xx
  have hc := binaryRecover InternalListCodec.consCode (observation Q) (InternalAcceptance.constantZero 3)
    (ys 2) (ys 1) z xx (hq 2) (hq 1) hz
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj (hq 0) (hq 1) hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
