module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowSyntaxAlgorithm (termParts termNext syntaxBits table)
open NumberedWindowInternalCoverSelectedValidityTargets

private theorem onLayout (term args : Nat → Bool) (tag : Nat) (fields : List Nat)
    (good : termParts term args tag fields = true) :
    (tag,fields.length) ∈ layout := by
  unfold termParts at good
  split at good <;> simp_all [layout]

private theorem knownTag (n tag arity : Nat) (fields : List Nat)
    (parsed : unpackNode n = some (tag,fields)) (len : fields.length = arity) :
    run (header tag arity) n = 1 := by
  unfold header
  have literalTag : run (literal 1 tag) n = tag := literalEvaluation 1 tag (n ::ᵥ nil)
  exact (nodeArity (literal 1 tag) arity n tag literalTag).2 ⟨fields,parsed,len⟩

private theorem dispatch (xs : List (Nat × Nat)) (n tag arity : Nat)
    (member : (tag,arity) ∈ xs) (got : run (header tag arity) n = 1) :
    run (headerAny xs) n = 1 := by
  induction xs with
  | nil => simp at member
  | cons pair rest ih =>
    obtain ⟨t,a⟩ := pair
    change evaluate (branch (GorbowVerifierNormalization.normalize (header t a))
      (headerAny rest) (InternalLessThan.constantOne 1)) (n ::ᵥ nil) = 1
    rw [evalBranch,evalNormalize]
    change (if (if run (header t a) n = 1 then 1 else 0) = 0
      then run (headerAny rest) n else run (InternalLessThan.constantOne 1) n) = 1
    have unit : run (InternalLessThan.constantOne 1) n = 1 := rfl
    by_cases head : run (header t a) n = 1
    · simp [head,unit]
    · have tail : (tag,arity) ∈ rest := by
        rcases List.mem_cons.mp member with same | has
        · cases same
          exact False.elim (head got)
        · exact has
      simp [head,ih tail]

private theorem validHeader (n : Nat) (good : (syntaxBits n).1 = true) :
    run (headerAny layout) n = 1 := by
  cases hd : unpackNode n with
  | none => simp [syntaxBits,termNext,hd] at good
  | some pair =>
    obtain ⟨tag,fields⟩ := pair
    have parts : termParts (fun q => ((table n).getD q (false,false)).1)
        (fun a => ((table n).getD a (false,false)).2) tag fields = true := by
      simpa [syntaxBits,termNext,hd] using good
    exact dispatch layout n tag fields.length (onLayout _ _ _ _ parts) (knownTag n tag _ fields hd rfl)

theorem exact_CoverSelectedValidityCalibration : ExactCoverSelectedValidityCalibration := by
  intro V cal n
  have v := cal n
  unfold selectedValidity run at *
  rw [actualConjunctionEvaluation,v]
  cases h : (syntaxBits n).1
  · simp [h]
  · have actual := validHeader n h
    change evaluate (headerAny layout) (n ::ᵥ nil) = 1 at actual
    simp [h,actual]

#print axioms exact_CoverSelectedValidityCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityNumericProof
