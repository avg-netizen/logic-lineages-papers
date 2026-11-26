module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalEqualityTestCompositionProof (equalityOfEqual)
open OriginalVariableDecoderEqualityProof (equalityReject)
open InternalCanonicalFixedWindowVertexDispatchSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHeadClassNumber
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal numeral inequality by successor cancellation alone. -/
theorem numeralDifferent (a b : Nat) (hne : a ≠ b) :
    Nonempty (Derivation body Delta (eqn (numeral a : OTerm alpha) (numeral b)).not) := by
  induction a generalizing b Delta with
  | zero =>
    cases b with
    | zero => exact False.elim (hne rfl)
    | succ b =>
      exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.zeroNeSuc
        (Derivation.hypothesis List.mem_cons_self))⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨InternalTagArithmeticSupportProof.sucNeZero (numeral a)⟩
    | succ b =>
      obtain ⟨h⟩ := ih (Delta := eqn (numeral (a+1) : OTerm alpha) (numeral (b+1)) :: Delta) b
        (fun he => hne (congrArg Nat.succ he))
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination h
        (InternalTagArithmeticSupportProof.cancelSuc (Derivation.hypothesis List.mem_cons_self)))⟩

theorem tagControl (tag test : Nat) (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag) payload))) :
    Nonempty (Derivation body Delta (graph1 (tagIs test) (if tag=test then suc z else z) raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  by_cases he : tag=test
  · subst test
    simp only [if_pos rfl]
    exact binaryValue InternalEqualityTest.equalityTest InternalUnpair.left
      (InternalCanonicalFixedWindowVertexDispatch.constant 1 tag) (suc z) (numeral tag) (numeral tag) xs
      (equalityOfEqual (numeral tag) (numeral tag) ⟨InternalTagArithmeticSupportProof.refl _⟩)
      (pairLeft raw (numeral tag) payload hp) (constantValue 1 tag xs)
  · simp only [if_neg he]
    exact binaryValue InternalEqualityTest.equalityTest InternalUnpair.left
      (InternalCanonicalFixedWindowVertexDispatch.constant 1 test) z (numeral tag) (numeral test) xs
      (equalityReject (numeral tag) (numeral test) (numeralDifferent tag test he))
      (pairLeft raw (numeral tag) payload hp) (constantValue 1 test xs)

theorem literalAt (tag : Nat) (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag) payload))) :
    Nonempty (Derivation body Delta (graph1 classNumber
      (if tag=4 then suc z else if tag=5 then suc (suc payload) else z) raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  let ranked : Program 1 := .composition .succ (fun _ : Fin 1 => .composition .succ (fun _ : Fin 1 => InternalUnpair.right))
  have h4 := tagControl tag 4 raw payload hp
  have h5 := tagControl tag 5 raw payload hp
  by_cases he4 : tag=4
  · simp only [he4,if_pos rfl] at h4 ⊢
    exact successorBranchIntro (tagIs 4)
      (InternalAcceptance.branch (tagIs 5) (InternalAcceptance.constantZero 1) ranked)
      (InternalLessThan.constantOne 1) (suc z) z xs h4 (InternalLessThanSupportProof.oneConstantValue xs)
  · simp only [if_neg he4] at h4 ⊢
    apply zeroBranchIntro (tagIs 4)
      (InternalAcceptance.branch (tagIs 5) (InternalAcceptance.constantZero 1) ranked)
      (InternalLessThan.constantOne 1) _ xs h4
    by_cases he5 : tag=5
    · simp only [if_pos he5] at h5 ⊢
      have hr := pairRight raw (numeral tag) payload hp
      have hs := unaryValue .succ InternalUnpair.right (suc payload) payload xs
        (successorValue (Fin.cons payload Fin.elim0)) hr
      have hss := unaryValue .succ (.composition .succ (fun _ : Fin 1 => InternalUnpair.right))
        (suc (suc payload)) (suc payload) xs (successorValue (Fin.cons (suc payload) Fin.elim0)) hs
      exact successorBranchIntro (tagIs 5) (InternalAcceptance.constantZero 1) ranked
        (suc (suc payload)) z xs h5 hss
    · simp only [if_neg he5] at h5 ⊢
      exact zeroBranchIntro (tagIs 5) (InternalAcceptance.constantZero 1) ranked z xs h5 (constantZeroValue xs)

theorem literalCases : OriginalHeadClassNumberTargets.LiteralCases := by
  intro body alpha Delta tag raw payload
  let A := graph2 InternalPairing.pairing raw (numeral tag) payload
  obtain ⟨h⟩ := literalAt tag raw payload (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberInternalProof
