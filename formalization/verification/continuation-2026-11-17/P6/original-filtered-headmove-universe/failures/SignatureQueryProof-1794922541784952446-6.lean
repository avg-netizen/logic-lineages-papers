module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.QueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SignatureQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem query (H : Program 1) (head : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (data result types : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 H data (head.relabel j))) →
      Nonempty (Derivation body Theta (OriginalTypedDecoderStepSpecification.StepArrowFields data result types)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalAcceptanceSupportProof.programCases H ![head] psi
  intro beta j Theta data hj hd
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hd
  apply Continuation20261117.OriginalStructuralContextClosure.QueryProof.fields data (psi.relabel j)
  intro eta k Xi result types hk hf
  have hd' := renameInto hd k Xi hk
  rw [graph1Rename] at hd'
  have h := next eta (k ∘ j) Xi (data.relabel k) result types
    (fun q hq => by simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (q.relabel j) (hj q hq))
  have he : Nonempty (Derivation body Xi (graph1 H (data.relabel k) (head.relabel (k ∘ j)))) := by
    simpa only [Term.relabel_relabel] using hd'
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h he hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SignatureQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SignatureQueryProof
