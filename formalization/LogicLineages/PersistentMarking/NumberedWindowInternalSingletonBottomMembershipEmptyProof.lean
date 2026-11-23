module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipEmpty
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowInternalSingletonBottomTargets (recognize)
open NumberedWindowInternalSingletonBottomBranchTargets (sourceSelector sourceControl targetBranch)
open NumberedWindowInternalSingletonBottomMembershipTargets (selectedDirect)
open NumberedWindowInternalSparsePathEnvelope (run exactBody applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (bodyArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (emptyUnpack)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (bothEvaluation)
open NumberedWindowInternalEmptyMultisetTargets (emptyGuard)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)

private theorem recognizerZero : run recognize 0 = 0 := by
  have missing : run (exactBody 1) 0 ≠ 1 := by
    intro h
    obtain ⟨l,hl,len⟩ := (bodyArity 1 0).mp h
    rw [emptyUnpack] at hl
    cases hl
    simp at len
  unfold run at missing
  unfold run recognize
  change evaluate (bothOne _ _) _ = _
  rw [bothEvaluation]
  exact if_neg (fun h => missing h.1)

private theorem graphAtZero {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 1) (hp : evaluate p (0 ::ᵥ nil) = 0) :
    Nonempty (Derivation B Γ (programGraph p z ![z])) := by
  have h := exact_NumeralGraph 1 p (0 ::ᵥ nil) B α Γ
  have eq : inputs (α := α) (0 ::ᵥ nil) = ![z] := by
    funext k
    exact Fin.cases rfl (fun j => Fin.elim0 j) k
  rw [hp,eq] at h
  exact h

private theorem controlAtEmpty {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (w y : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (programGraph sourceControl z ![z,w,y])) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![z,w,y]
  have selected : Nonempty (Derivation B Γ (programGraph sourceSelector z xs)) := by
    unfold sourceSelector
    apply compositionValue recognize (fun _ : Fin 1 => .projection (0 : Fin 3)) z xs ![z]
    · exact graphAtZero recognize recognizerZero
    · intro k
      obtain rfl := Fin.eq_zero k
      exact projectionValue 0 xs
  have norm : Nonempty (Derivation B Γ
      (programGraph GorbowVerifierNormalization.equalsOne z (Fin.cons z Fin.elim0))) :=
    graphAtZero GorbowVerifierNormalization.equalsOne
      (GorbowVerifierNormalization.Proof.actualEvaluation.1 0)
  exact normalizeValue sourceSelector z z xs norm selected

private theorem selectedAtEmpty {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d : Program 3) (w y : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (programGraph (selectedDirect d) z ![z,w,y])) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![z,w,y]
  have inner : Nonempty (Derivation B Γ (programGraph (emptyGuard d) z xs)) :=
    zeroBranchIntro (.projection 0) (constantZero 3) d z xs
      (projectionValue 0 xs) (constantZeroValue xs)
  exact zeroBranchIntro sourceControl (emptyGuard d) (targetBranch (emptyGuard d))
    z xs (controlAtEmpty w y) inner

private theorem rawOddCertificate {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (i j : Program 1) (r D : Program 3) (c : Nat) (y w : OrdinaryArithmetic.Term α)
    (cert : Nonempty (Derivation B Γ (certificate (data i j r D) true c z y w))) :
    Nonempty (Derivation B Γ (programGraph D (suc z) ![z,w,y])) := by
  have h := (exact_CertificateRules i j r D true c B α Γ z y w).1 cert
  exact h

private theorem rejectRawEmpty {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d : Program 3) (y w : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph (selectedDirect d) (suc z) ![z,w,y]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have miss : Nonempty (Derivation B Γ (programGraph (selectedDirect d) z ![z,w,y])) :=
    selectedAtEmpty d w y
  obtain ⟨bad⟩ := valueUnique (selectedDirect d) (suc z) z ![z,w,y] hit miss
  exact ⟨sucNeZeroApply bad⟩

attribute [local irreducible] selectedDirect

/-- The exact new checker still forbids any empty-source certificate.
The witness and destination may both be arbitrary free object terms. -/
theorem rejectEmpty (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (y w : OrdinaryArithmetic.Term α) :
    let S := data i j r (selectedDirect d)
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S true c OrdinaryArithmetic.zeroTerm y w)) →
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let D := selectedDirect d
  let S := data i j r D
  let B := sourceBody S c
  change Nonempty (Derivation B Γ
    (certificate (data i j r D) true c OrdinaryArithmetic.zeroTerm y w)) →
      Nonempty (Derivation B Γ (⊥ : Formula α))
  intro cert
  have hit : Nonempty (Derivation B Γ (programGraph D (suc z) ![z,w,y])) :=
    rawOddCertificate i j r D c y w cert
  exact rejectRawEmpty d y w hit

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipEmpty
