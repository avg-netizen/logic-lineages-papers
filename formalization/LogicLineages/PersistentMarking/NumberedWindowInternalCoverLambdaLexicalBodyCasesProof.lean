module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBodyReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBodyCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof (positiveBranchCases unitCheckedBranch)
open NumberedWindowInternalCoverLambdaLexicalBodyReportsProof (actualLambdaDomainK recoverPrecedingLambdaChild)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough moveStoredK)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualLambdaBodyCases (s : Settings) (B : Program 2) (T : Program 1) (ctx ty q res : OTerm α)
    (Q : Formula α)
    (gate : Nonempty (Derivation body Γ (programGraph (lambdaPositive s B T) (suc res) ![ctx,lambdaTerm ty q])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (childTy : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      ActualPrecedingLambdaChild s B T body Δ (ctx.relabel j) (ty.relabel j) (q.relabel j)
        (res.relabel j) childTy →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  apply positiveBranchCases B (lambdaCheckedDomain s B T) ctx (lambdaTerm ty q) res Q gate
  intro β j Δ ignored keep original selected
  rw [lambdaRename] at selected
  let ctx' := ctx.relabel j
  let dom := ty.relabel j
  let child := q.relabel j
  let r := res.relabel j
  let raw := lambdaTerm dom child
  have domainReport := unitCheckedBranch (onRaw (leafTypeTest s)) (lambdaCheckedBody s B T) ctx' raw r selected
  have actualK := actualLambdaDomainK s ctx' dom child domainReport.1
  apply positiveBranchCases (lambdaOldBody s B T) (lambdaLexicalResult s B T)
    ctx' raw r (Q.relabel j) domainReport.2
  intro γ g Ξ childTy retain oldChild arrowResult
  change Nonempty (Derivation body Ξ
    (programGraph (lambdaOldBody s B T) (suc childTy) ![ctx'.relabel g,(lambdaTerm dom child).relabel g])) at oldChild
  change Nonempty (Derivation body Ξ
    (programGraph (lambdaLexicalResult s B T) (suc (r.relabel g))
      ![ctx'.relabel g,(lambdaTerm dom child).relabel g])) at arrowResult
  rw [lambdaRename] at oldChild arrowResult
  have paid := recoverPrecedingLambdaChild s B T (ctx'.relabel g) (dom.relabel g) (child.relabel g)
    (r.relabel g) childTy (moveStoredK s g retain dom actualK) oldChild arrowResult
  have both := keepThrough j g keep retain
  have same : ActualPrecedingLambdaChild s B T body Ξ (ctx.relabel (g ∘ j)) (ty.relabel (g ∘ j))
      (q.relabel (g ∘ j)) (res.relabel (g ∘ j)) childTy := by
    simpa only [ctx',dom,child,r,Term.relabel_relabel] using paid
  rw [formulaRelabelComposition j g Q]
  exact next γ (g ∘ j) Ξ childTy both same

#print axioms actualLambdaBodyCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBodyCasesProof
