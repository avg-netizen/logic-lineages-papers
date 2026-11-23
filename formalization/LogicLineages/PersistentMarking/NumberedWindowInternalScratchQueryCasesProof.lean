module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus
open InternalGraphComposition InternalControlGraph
open InternalAcceptanceSupportProof (programCases programCompositionCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem queryCases {m n : Nat} (qs : Fin n → Program m) (xs : Fin m → OTerm alpha)
    (psi : Formula alpha)
    (h : ∀ (beta : Type) (j : alpha → beta) (ys : Fin n → OTerm beta) (Theta : List (Formula beta)),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      (∀ i, Nonempty (Derivation body Theta
        (programGraph (qs i) (ys i) (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases (.composition (InternalAcceptance.constantZero n) qs) xs _
  intro beta j Theta v hj hv
  apply programCompositionCases (InternalAcceptance.constantZero n) qs v
    (fun a => (xs a).relabel j) _ hv
  intro gamma k ys Xi hk _ hg
  have hm : ∀ r ∈ Delta, r.relabel (k ∘ j) ∈ Xi := by
    intro r hr
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (r.relabel j) (hj r hr)
  have hg' : ∀ i, Nonempty (Derivation body Xi
      (programGraph (qs i) (ys i) (fun a => (xs a).relabel (k ∘ j)))) := by
    intro i
    simpa only [Term.relabel_relabel] using hg i
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h gamma (k ∘ j) ys Xi hm hg'

/-- Definitional relabel law, independent of decoder transport. -/
theorem notRename {alpha beta : Type} (P : Formula alpha) (j : alpha → beta) :
    P.not.relabel j = (P.relabel j).not := rfl

#print axioms queryCases
end LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
