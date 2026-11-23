module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanEvaluationProof (exactLessThanEvaluation)
open ID1Completion.InternalLessThanProof (lessOfAcceptance)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)
open NumberedWindowCopyAlgorithm (Entries copy)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowRootDispatchAlgorithm (check fixed parts)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowInternalCopyHeadConeNumericProof (exact_OriginalCopyHeadCone)
open NumberedWindowInternalCopyHeadClosedRootTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem concreteCopyPayloadSpec (entries : Entries) (s : Settings) (src dst : Nat) :
    concreteCopyRoot entries s src copyPayload dst = copy entries s.window.2 src dst := by
  change NumberedWindowConcreteCheckers.root entries s src copyPayload dst = _
  unfold NumberedWindowConcreteCheckers.root check copyPayload
  rw [nodePacked] <;> rfl

private theorem numeralRankOrder (n m : Nat) (h : n < m) :
    D B Γ (ltF (numeral n) (numeral m)) := by
  let v := n ::ᵥ m ::ᵥ List.Vector.nil
  have dv : evaluate ltTest v = 1 := by
    change evaluate ltTest (n ::ᵥ m ::ᵥ List.Vector.nil) = 1
    rw [exactLessThanEvaluation,if_pos h]
  have d := exact_NumeralGraph 2 ltTest v B α Γ
  have args : (inputs v : Fin 2 → OTerm α) =
      Fin.cons (numeral n) (Fin.cons (numeral m) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [dv,args] at d
  exact lessOfAcceptance (numeral n) (numeral m) d

/-- A genuine accepting closed graph of the same actual root at the
literal copy payload enters the copy cone. A rejected concrete branch
is disposed of by original object graph functionality, not by claiming
an ambient meta-level equation from an arbitrary object derivation. -/
theorem exact_OriginalClosedCopyRootCone : ExactOriginalClosedCopyRootCone := by
  intro entries s root fit B α Γ src dst f ty label base extras g args goal accepted
  rintro ⟨srcView,dstView,next⟩
  cases success : copy entries s.window.2 src dst with
  | false =>
    let v := src ::ᵥ copyPayload ::ᵥ dst ::ᵥ List.Vector.nil
    have ev : evaluate root v = 0 := by
      change evaluate root (src ::ᵥ copyPayload ::ᵥ dst ::ᵥ List.Vector.nil) = 0
      rw [fit,concreteCopyPayloadSpec,success] <;> rfl
    have d := exact_NumeralGraph 3 root v B α Γ
    have args : (inputs v : Fin 3 → OTerm α) = ![numeral src,numeral copyPayload,numeral dst] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
    rw [ev,args] at d
    obtain ⟨bad⟩ := valueUnique root (suc z) z
      (![numeral src,numeral copyPayload,numeral dst] : Fin 3 → OTerm α) accepted d
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  | true =>
    obtain ⟨inHeads,resultType,rf,rg,fromRank,toRank,smaller⟩ :=
      exact_OriginalCopyHeadCone entries s.window.2 src dst f ty label base extras g args
        srcView dstView success
    exact next inHeads resultType rf rg fromRank toRank (numeralRankOrder rg rf smaller)

#print axioms exact_OriginalClosedCopyRootCone

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootProof
