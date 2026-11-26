module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOriginAndConsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseParsedFoldProof (ParsedFoldCases exact_OriginalSparseParsedFold)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof (exact_LiteralConditionalJUnion)
open NumberedWindowInternalDirectTypedScratchConsProof (exact_TypedScratchCons)
open NumberedWindowInternalLiteralOriginAndConsProof (exact_LiteralRawConsUnionReport)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr CertifiedOriginSplit)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof
open NumberedWindowInternalLiteralSparseJFoldSupportProof

private theorem consProgress (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (promote : LiteralScalarSingletonPromotion i r c) {α : Type}
    (Γ : List (Formula α)) (n s h t st : OTerm α)
    (shape : Pr (literalData i r) c Γ (eqn n (rawCons h t)))
    (tailParse : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc st) ![t])
    (scratch : Report (B := sourceBody (literalData i r) c) (Γ := Γ) consCode s ![h,st])
    (lower : Pr (literalData i r) c Γ (jCondition i t st))
    (typed : Pr (literalData i r) c Γ (typedAt i s))
    (all : Pr (literalData i r) c Γ (scalarMembers s)) :
    Pr (literalData i r) c Γ (membership true n) := by
  let S := literalData i r
  let B := sourceBody S c
  have cell : Nonempty (Derivation B Γ (consGraph s h st)) := scratch
  obtain ⟨typedSplit⟩ := exact_TypedScratchCons i B α Γ s h st cell typed
  have headOcc := headMember s h st h cell ⟨refl h⟩
  have headI := applyScalarMembers s h all headOcc
  have headJ : Pr S c Γ (membership true (singletonCode h)) :=
    promote α Γ h headI ⟨Derivation.conjunctionLeft typedSplit⟩
  have tailAll := scalarMembersOfTail s h st cell all
  obtain ⟨tailAll⟩ := tailAll
  obtain ⟨lower⟩ := lower
  have tailJ : Pr S c Γ (membership true t) :=
    ⟨Derivation.implicationElimination
      (Derivation.implicationElimination lower (Derivation.conjunctionRight typedSplit)) tailAll⟩
  have joined := exact_LiteralRawConsUnionReport h t st tailParse
  have rawJ := exact_LiteralConditionalJUnion i r c splitter α Γ (singletonCode h) t
    (rawCons h t) headJ tailJ joined
  obtain ⟨shape⟩ := shape
  exact moveJ (rawCons h t) n ⟨symm shape⟩ rawJ

private theorem literalJCases (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (empty : LiteralEmptyMembership i r c) (promote : LiteralScalarSingletonPromotion i r c)
    (α : Type) (Γ : List (Formula α)) :
    ParsedFoldCases (sourceBody (literalData i r) c) Γ (jMotive (α := α) i) := by
  constructor
  · intro β j Δ n s _ rawZero _
    rw [jMotiveAt]
    obtain ⟨rawZero⟩ := rawZero
    have base := moveJ z n ⟨symm rawZero⟩ (empty β Δ)
    obtain ⟨done⟩ := addTwoHypotheses (typedAt i s) (scalarMembers s) base
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction done)⟩
  · intro β j Δ n s h t st _ _ _ eqRaw _ tail scratch lower
    rw [jMotiveAt] at lower ⊢
    let P := typedAt i s
    let Q := scalarMembers s
    let Ξ := Q :: P :: Δ
    have typed : Pr (literalData i r) c Ξ P :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have all : Pr (literalData i r) c Ξ Q :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨done⟩ := consProgress i r c splitter promote Ξ n s h t st
      (addTwoHypotheses P Q eqRaw) (addTwoHypotheses P Q tail)
      (addTwoHypotheses P Q scratch) (addTwoHypotheses P Q lower) typed all
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction done)⟩

/-- An internal J fold for arbitrary original positive parsed codes, with
actual typed scratch and actual scalar I for each original member. No
host list, untyped membership or other installed checker is substituted. -/
theorem exact_LiteralSparseParsedJFold (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (empty : LiteralEmptyMembership i r c) (promote : LiteralScalarSingletonPromotion i r c)
    (α : Type) (Γ : List (Formula α)) (n s : OTerm α)
    (parsed : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc s) ![n])
    (typed : Pr (literalData i r) c Γ (typedAt i s))
    (all : Pr (literalData i r) c Γ (scalarMembers s)) :
    Pr (literalData i r) c Γ (membership true n) := by
  have condition := exact_OriginalSparseParsedFold (jMotive (α := α) i)
    (literalJCases i r c splitter empty promote α Γ) n s parsed
  rw [jMotiveAt] at condition
  obtain ⟨condition⟩ := condition
  obtain ⟨typed⟩ := typed
  obtain ⟨all⟩ := all
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination condition typed) all⟩

#print axioms exact_LiteralSparseParsedJFold

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldProof
