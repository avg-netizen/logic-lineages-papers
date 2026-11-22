module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof (unitCheckedBranch positiveBranchCases)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaPositive lambdaCheckedDomain)
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenCoverRestrictedLambdaFragmentBase : ExactOpenCoverRestrictedLambdaFragmentBase := by
  intro B body α Γ ctx dom q out actual
  let raw := lambdaTerm dom q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) dom q
  have headerPass := liftRawReport (header 2 2) ctx raw (suc z) shape.lambdaYes
  have chose := successorBranchElim (onRaw (header 2 2)) B (lambdaFragmentCheckedBase B)
    (suc out) z xs headerPass actual
  have callback := (unitCheckedBranch (onRaw lambdaFragmentBodyCode) B ctx raw out chose).1
  have read : Nonempty (Derivation body Γ (unary lambdaFragmentBodyCode (suc z) raw)) := by
    apply compositionRecover lambdaFragmentBodyCode (fun _ : Fin 1 => Program.projection 1)
      (suc z) xs ![raw] callback
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  apply compositionRecover fragmentGuard (fun _ : Fin 1 => field 1) (suc z) ![raw] ![q] read
  intro i
  obtain rfl := Fin.eq_zero i
  exact shape.childRead

theorem guardAtPositiveLambda (s : Settings) (B : Program 2) (T : Program 1) (ctx dom q out : OTerm α)
    (actual : Nonempty (Derivation body Γ
      (programGraph (lambdaPositive s (lambdaFragmentBase B) T) (suc out) ![ctx,lambdaTerm dom q]))) :
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q)) := by
  let Z := unary fragmentGuard (suc z) q
  apply positiveBranchCases (lambdaFragmentBase B) (lambdaCheckedDomain s (lambdaFragmentBase B) T)
    ctx (lambdaTerm dom q) out Z actual
  intro β j Δ control keep positive _
  rw [lambdaRename] at positive
  simp only [Z,unaryRename,sucRelabel,zRelabel]
  exact exact_OpenCoverRestrictedLambdaFragmentBase B body β Δ (ctx.relabel j) (dom.relabel j)
    (q.relabel j) control positive

#print axioms exact_OpenCoverRestrictedLambdaFragmentBase
#print axioms guardAtPositiveLambda

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof
