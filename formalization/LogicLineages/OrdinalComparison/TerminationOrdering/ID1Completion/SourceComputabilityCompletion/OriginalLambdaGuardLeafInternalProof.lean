module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaGuardLeaf
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem combine {P Q : Formula alpha}
    (hp : Nonempty (Derivation body Delta P)) (hq : Nonempty (Derivation body Delta Q)) :
    Nonempty (Derivation body Delta (P ⊓ Q)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction hp hq⟩

theorem projectLeft {P Q : Formula alpha} (h : Nonempty (Derivation body Delta (P ⊓ Q))) :
    Nonempty (Derivation body Delta P) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionLeft h⟩

theorem projectRight {P Q : Formula alpha} (h : Nonempty (Derivation body Delta (P ⊓ Q))) :
    Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionRight h⟩

/-- Functionality of the original graph excludes exact-one acceptance when
its same-input output is zero. This uses no numerical evaluation. -/
theorem zeroGraphNotOne {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p z xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs).not) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨he⟩ := valueUnique p (suc z) z xs
    (show Nonempty (Derivation body (programGraph p (suc z) xs :: Delta)
      (programGraph p (suc z) xs)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hp _⟩
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem originalFactor (oldStep : Program 4) :
    OriginalConstructorLeaf.OriginalFactor oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := projectLeft (conjunctionRecover oldStep (guard oldStep) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem leafHasGuard (oldStep : Program 4) : LeafHasGuard oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := projectRight (conjunctionRecover oldStep (guard oldStep) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The two normalized control graphs select the literal child-guard branch
at the unchanged source, target, certificate and parameter. -/
theorem recoverChildBranch (oldStep : Program 4)
    (source target certificate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (accepted (refined oldStep) source target certificate parameter ⊓
        LambdaNonbottom source target certificate parameter))) :
    Nonempty (Derivation body Delta
      (accepted matchingTarget source target certificate parameter ⊓
        accepted (childCheck oldStep) source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hg := projectRight (conjunctionRecover oldStep (guard oldStep) xs (projectLeft ha))
  have hlambda := projectLeft (projectRight ha)
  have hnonbottom := projectRight (projectRight ha)
  have hinner := successorBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize sourceLambda)
    (InternalLessThan.constantOne 4)
    (InternalAcceptance.branch
      (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize sameBottom)
      (childGuard oldStep) (InternalLessThan.constantOne 4))
    (suc z) z xs (normalizeAccept sourceLambda xs hlambda) hg
  have hchild := zeroBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize sameBottom)
    (childGuard oldStep) (InternalLessThan.constantOne 4) (suc z) xs
    (normalizeReject sameBottom xs (zeroGraphNotOne sameBottom xs hnonbottom)) hinner
  exact conjunctionRecover matchingTarget (childCheck oldStep) xs hchild

theorem leafHasChildBranch (oldStep : Program 4) :
    LeafHasChildBranch oldStep (refined oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := accepted (refined oldStep) source target certificate parameter ⊓
    LambdaNonbottom source target certificate parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := recoverChildBranch oldStep source target certificate parameter hp
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalLambdaGuardLeafInternalCases :
    OriginalLambdaGuardLeafTargets.ActualOriginalLambdaGuardLeafInternalCases := by
  intro oldStep
  exact ⟨originalFactor oldStep,leafHasGuard oldStep,leafHasChildBranch oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafInternalProof
