module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalSourceIntroductionSyntaxProof
open InternalOriginalOrderSyntaxProof (notSubst)
open InternalRecursionClosureSyntaxProof (conjunctionSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof (symm trans refl)
open InternalTagArithmeticSyntaxProof (eqn)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderInternalBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem orRename {beta : Type} (P Q : Formula alpha) (j : alpha → beta) :
    (P ⊔ Q).relabel j = P.relabel j ⊔ Q.relabel j := by
  simp only [formulaRelabelAsSubst,orSubst]

@[simp] theorem andRename {beta : Type} (P Q : Formula alpha) (j : alpha → beta) :
    (P ⊓ Q).relabel j = P.relabel j ⊓ Q.relabel j := by
  simp only [formulaRelabelAsSubst,conjunctionSubst]

@[simp] theorem notRename {beta : Type} (P : Formula alpha) (j : alpha → beta) :
    P.not.relabel j = (P.relabel j).not := by
  simp only [formulaRelabelAsSubst,notSubst]

theorem contradiction {P Q : Formula alpha}
    (hp : Nonempty (Derivation body Delta P))
    (hn : Nonempty (Derivation body Delta P.not)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hp)⟩

theorem numeralConflict (m n : Nat) (hmn : m ≠ n) (Q : Formula alpha)
    (h : Nonempty (Derivation body Delta (equal (numeral m) (numeral n)))) :
    Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.explosion (numeralNeApply m n hmn (by simpa only [equalEqn] using h))⟩

theorem excludeNumeral (x : OTerm alpha) (m n : Nat) (hmn : m ≠ n)
    (h : Nonempty (Derivation body Delta (equal x (numeral m)))) :
    Nonempty (Derivation body Delta (equal x (numeral n)).not) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply numeralNeApply m n hmn
  exact trans (symm (by simpa only [equalEqn] using InternalBetaTotalityProof.addHyp h (equal x (numeral n))))
    (by simpa only [equalEqn] using
      (Derivation.hypothesis List.mem_cons_self : Derivation body
        (equal x (numeral n) :: Delta) (equal x (numeral n))))

/-- A proof-only syntax certificate for literal zero/one leaves. Arbitrary
programs may occur in tests. No evaluation is used to certify their outputs. -/
inductive BooleanTree {n : Nat} : Program n → Prop
  | zero : BooleanTree (constant n 0)
  | one : BooleanTree (constant n 1)
  | branch (p q yes no : Program n) : BooleanTree yes → BooleanTree no →
      BooleanTree (ifSame p q yes no)

theorem booleanRange {n : Nat} {P : Program n} (tree : BooleanTree P)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ho : Nonempty (Derivation body Delta (programGraph P out xs))) :
    Nonempty (Derivation body Delta (equal out (numeral 0) ⊔ equal out (numeral 1))) := by
  induction tree generalizing alpha with
  | zero =>
    obtain ⟨h⟩ := constantForward 0 out xs ho
    exact ⟨orLeft h⟩
  | one =>
    obtain ⟨h⟩ := constantForward 1 out xs ho
    exact ⟨orRight h⟩
  | branch p q yes no hy hn ihy ihn =>
    apply queryCases (![p,q] : Fin 2 → Program n) xs _
    intro beta j ys Theta hj hq
    have ho' := renameInto ho j Theta hj
    rw [programRename] at ho'
    have hc := sameForward p q yes no (out.relabel j) (ys 0) (ys 1)
      (fun i => (xs i).relabel j) (hq 0) (hq 1) ho'
    simp only [orRename,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,
      OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel]
    apply orCases hc
    · exact ihy _ _ (andRight (show Nonempty (Derivation body
        ((equal (ys 0) (ys 1) ⊓ programGraph yes (out.relabel j) (fun i => (xs i).relabel j)) :: Theta)
        (equal (ys 0) (ys 1) ⊓ programGraph yes (out.relabel j) (fun i => (xs i).relabel j))) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
    · exact ihn _ _ (andRight (show Nonempty (Derivation body
        (((equal (ys 0) (ys 1)).not ⊓ programGraph no (out.relabel j) (fun i => (xs i).relabel j)) :: Theta)
        ((equal (ys 0) (ys 1)).not ⊓ programGraph no (out.relabel j) (fun i => (xs i).relabel j))) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))

/-- Accepting a test-filter forces the arbitrary test's output to be exactly
one, and retains the entire accepting branch. -/
theorem filterForward {n : Nat} (test yes : Program n) (xs : Fin n → OTerm alpha)
    (ho : Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes (constant n 0)) (numeral 1) xs))) :
    Nonempty (Derivation body Delta
      (programGraph test (numeral 1) xs ⊓ programGraph yes (numeral 1) xs)) := by
  apply programCases test xs _
  intro beta j Theta value hj hv
  have ho' := renameInto ho j Theta hj
  simp only [andRename,notRename,programRename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel] at ho'
  simp only [andRename,notRename,programRename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel]
  let xx := fun i => (xs i).relabel j
  have hc := sameForward test (constant n 1) yes (constant n 0)
    (numeral 1) value (numeral 1) xx hv (constantValue 1 xx) ho'
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal value (numeral 1) ⊓ programGraph yes (numeral 1) xx) :: Theta)
        (equal value (numeral 1) ⊓ programGraph yes (numeral 1) xx)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact andIntro (outputTransport test value (numeral 1) xx
      (by simpa only [equalEqn] using andLeft hh) (withHyp hv _)) (andRight hh)
  · have hh : Nonempty (Derivation body
        (((equal value (numeral 1)).not ⊓ programGraph (constant n 0) (numeral 1) xx) :: Theta)
        ((equal value (numeral 1)).not ⊓ programGraph (constant n 0) (numeral 1) xx)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact numeralConflict 1 0 (by decide) _ (constantForward 0 (numeral 1) xx (andRight hh))

theorem filterBackward {n : Nat} (test yes : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs)))
    (hy : Nonempty (Derivation body Delta (programGraph yes (numeral 1) xs))) :
    Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes (constant n 0)) (numeral 1) xs)) :=
  sameYesIntro test (constant n 1) yes (constant n 0) (numeral 1) (numeral 1) (numeral 1)
    xs ht (constantValue 1 xs) (by simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn (numeral 1 : OTerm alpha) (numeral 1))) from ⟨refl _⟩)) hy

/-- Totality plus the checked zero/one range supplies actual rejection; absence
of acceptance is not silently identified with a graph value. -/
theorem booleanReject {n : Nat} {P : Program n} (tree : BooleanTree P)
    (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (programGraph P (numeral 1) xs).not)) :
    Nonempty (Derivation body Delta (programGraph P (numeral 0) xs)) := by
  apply programCases P xs _
  intro beta j Theta value hj hv
  have hn' := renameInto hn j Theta hj
  simp only [andRename,notRename,programRename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel] at hn' ⊢
  let xx := fun i => (xs i).relabel j
  apply orCases (booleanRange tree value xx hv)
  · have hz : Nonempty (Derivation body (equal value (numeral 0) :: Theta) (equal value (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact outputTransport P value (numeral 0) xx (by simpa only [equalEqn] using hz) (withHyp hv _)
  · have he : Nonempty (Derivation body (equal value (numeral 1) :: Theta) (equal value (numeral 1))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact contradiction (outputTransport P value (numeral 1) xx
      (by simpa only [equalEqn] using he) (withHyp hv _)) (withHyp hn' _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
