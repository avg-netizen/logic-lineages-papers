module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Strong all-input arity classification. Nonzero arity retains the literal
original tag graph; zero arity makes no source-domain assertion. -/
def ArityView (out raw : OTerm alpha) : Formula alpha :=
  equal out (numeral 0) ⊔
    ((equal out (numeral 1) ⊓
      (graph1 rawTag (numeral 1) raw ⊔ graph1 rawTag (numeral 4) raw)) ⊔
     (equal out (numeral 2) ⊓
      (graph1 rawTag (numeral 2) raw ⊔
        (graph1 rawTag (numeral 5) raw ⊔ graph1 rawTag (numeral 7) raw))))

theorem orRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

@[simp] theorem arityViewRename {beta : Type} (out raw : OTerm alpha) (j : alpha → beta) :
    (ArityView out raw).relabel j = ArityView (out.relabel j) (raw.relabel j) := by
  simp only [ArityView,orRename,conjunctionRename,
    InternalControlGraphSupportProof.equalEqn,
    InternalTagArithmeticSyntaxProof.eqnRelabel,InternalTagArithmeticSyntaxProof.sucRelabel,
    zRelabel,SourceComputabilityFormulaSupportProof.numeral,graph1Rename]

theorem arityViewAtTag (raw tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) out raw))) :
    Nonempty (Derivation body Delta (ArityView out raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have ht0 := unaryValue InternalUnpair.left (.projection 0) tag raw xs ht (projectionValue 0 xs)
  apply numeralBranchCases (leftOf (.projection 0)) _ _ tag 1 out xs (ArityView out raw) ht0 ha
  · intro Theta0 inc0 hn0
    have ht1 := weakenProof ht0 inc0
    apply numeralBranchCases (leftOf (.projection 0)) _ _ tag 4 out xs (ArityView out raw) ht1 hn0
    · intro Theta1 inc1 hn1
      have ht2 := weakenProof ht1 inc1
      apply numeralBranchCases (leftOf (.projection 0)) _ _ tag 2 out xs (ArityView out raw) ht2 hn1
      · intro Theta2 inc2 hn2
        have ht3 := weakenProof ht2 inc2
        apply numeralBranchCases (leftOf (.projection 0)) _ _ tag 5 out xs (ArityView out raw) ht3 hn2
        · intro Theta3 inc3 hn3
          have ht4 := weakenProof ht3 inc3
          apply numeralBranchCases (leftOf (.projection 0)) _ _ tag 7 out xs (ArityView out raw) ht4 hn3
          · intro Theta4 inc4 hn4
            have ht5 := weakenProof ht4 inc4
            obtain ⟨he⟩ := valueUnique (constant 1 0) out (numeral 0) xs hn4 (constantValue 0 xs)
            exact ⟨orLeft (by simpa only [equalEqn] using he)⟩
          · intro Theta4 inc4 hv4 hc4
            obtain ⟨he⟩ := valueUnique (constant 1 2) out (numeral 2) xs hc4 (constantValue 2 xs)
            obtain ⟨hg⟩ := unaryRecover InternalUnpair.left (.projection 0) (numeral 7) raw xs hv4 (projectionValue 0 xs)
            exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight (orRight hg))))⟩
        · intro Theta3 inc3 hv3 hc3
          obtain ⟨he⟩ := valueUnique (constant 1 2) out (numeral 2) xs hc3 (constantValue 2 xs)
          obtain ⟨hg⟩ := unaryRecover InternalUnpair.left (.projection 0) (numeral 5) raw xs hv3 (projectionValue 0 xs)
          exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight (orLeft hg))))⟩
      · intro Theta2 inc2 hv2 hc2
        obtain ⟨he⟩ := valueUnique (constant 1 2) out (numeral 2) xs hc2 (constantValue 2 xs)
        obtain ⟨hg⟩ := unaryRecover InternalUnpair.left (.projection 0) (numeral 2) raw xs hv2 (projectionValue 0 xs)
        exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orLeft hg)))⟩
    · intro Theta1 inc1 hv1 hc1
      obtain ⟨he⟩ := valueUnique (constant 1 1) out (numeral 1) xs hc1 (constantValue 1 xs)
      obtain ⟨hg⟩ := unaryRecover InternalUnpair.left (.projection 0) (numeral 4) raw xs hv1 (projectionValue 0 xs)
      exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight hg)))⟩
  · intro Theta0 inc0 hv0 hc0
    obtain ⟨he⟩ := valueUnique (constant 1 1) out (numeral 1) xs hc0 (constantValue 1 xs)
    obtain ⟨hg⟩ := unaryRecover InternalUnpair.left (.projection 0) (numeral 1) raw xs hv0 (projectionValue 0 xs)
    exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orLeft hg)))⟩

/-- Every arithmetic raw number is covered, independently of source syntax. -/
theorem arityView (raw out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) out raw))) :
    Nonempty (Derivation body Delta (ArityView out raw)) := by
  apply programCases rawTag (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [arityViewRename]
  simp only [consTermRename,emptyRename] at ht
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename] at ha'
  exact arityViewAtTag (raw.relabel j) tag (out.relabel j) ht ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityProof
