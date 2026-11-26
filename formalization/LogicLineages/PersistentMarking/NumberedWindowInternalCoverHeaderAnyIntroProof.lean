module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderAnyIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header headerAt headerAny)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualHeaderAnyIntro (flags : List (Nat × Nat)) (tag arity : Nat) (q : OTerm α)
    (included : (tag,arity) ∈ flags)
    (actual : Nonempty (Derivation body Γ (headerAt tag arity q))) :
    Nonempty (Derivation body Γ (unary (headerAny flags) (suc z) q)) := by
  induction flags generalizing Γ with
  | nil => simp at included
  | cons entry rest ih =>
    obtain ⟨t,a⟩ := entry
    rcases List.mem_cons.mp included with same | later
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      exact successorBranchIntro (normalize (header tag arity)) (headerAny rest) (constantOne 1)
        (suc z) z ![q] (normalizeAccept (header tag arity) ![q] actual) (oneConstantValue ![q])
    · let A := headerAt t a q
      apply formulaCases A _
      · have first : Nonempty (Derivation body (A :: Γ) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        exact successorBranchIntro (normalize (header t a)) (headerAny rest) (constantOne 1)
          (suc z) z ![q] (normalizeAccept (header t a) ![q] first) (oneConstantValue ![q])
      · have no : Nonempty (Derivation body (A.not :: Γ) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        exact zeroBranchIntro (normalize (header t a)) (headerAny rest) (constantOne 1)
          (suc z) ![q] (normalizeReject (header t a) ![q] no) (ih later (withHyp actual A.not))

#print axioms actualHeaderAnyIntro

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderAnyIntroProof
