module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalListCodecSupportProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanCases (count role typ raw jobs : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (previous value singleton : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph5 scan previous (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j))) →
      Nonempty (Derivation body Theta
        (graph5 cell value (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j))) →
      Nonempty (Derivation body Theta (consGraph singleton value z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let single : Program 5 := .composition InternalListCodec.consCode
    ![cell,InternalAcceptance.constantZero 5]
  let qs : Fin 3 → Program 5 := ![scan,cell,single]
  let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 5 → OTerm beta := Fin.cons (count.relabel j)
    (Fin.cons (role.relabel j) (Fin.cons (typ.relabel j) (Fin.cons (raw.relabel j) (Fin.cons (jobs.relabel j) Fin.elim0))))
  have he : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
  rw [he] at hq
  have hz := InternalRawListRecursionSupportProof.constantZero (body := body) (Gamma := Theta) xx
  have hc := binaryRecover InternalListCodec.consCode cell (InternalAcceptance.constantZero 5)
    (ys 2) (ys 1) z xx (hq 2) (hq 1) hz
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj (hq 0) (hq 1) hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthCasesProof
