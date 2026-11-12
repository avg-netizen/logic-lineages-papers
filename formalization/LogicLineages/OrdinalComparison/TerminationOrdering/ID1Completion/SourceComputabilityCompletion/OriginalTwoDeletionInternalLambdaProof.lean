module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof hiding andIntro andLeft andRight
open OriginalRawSyntaxTransport
open OriginalTwoDeletionInternalDefinitions OriginalTwoDeletionInternalBindingProof OriginalTwoDeletionInternalSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalRawSyntaxTransportInternalFoldLambdaProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaAt4 (raw metadata child a b i j upper lower left right uc lc xc yc : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph3 (fold .erase) uc b (suc (suc j)) child)))
    (h1 : Nonempty (Derivation body Delta (graph3 (fold .erase) lc a (suc i) child)))
    (h2 : Nonempty (Derivation body Delta (graph3 (fold .erase) xc a (suc i) uc)))
    (h3 : Nonempty (Derivation body Delta (graph3 (fold .erase) yc b (suc j) lc)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  have hshape := lambdaFields raw i metadata child hc
  have hsmall := unaryChildStrict raw child (andLeft hshape) (andLeft (andRight hshape))
  have hbound := InternalRecursionGraphExtensionSupportProof.successorOrder i (suc j) (andLeft hf)
  have he := belowRawApply (fold .erase) raw child a b (suc i) (suc j) uc lc xc yc hi hsmall
    (andIntro hbound (andIntro h0 (andIntro h2 (andIntro h1 h3))))
  have hu := lambdaForward .erase raw upper b (suc j) metadata child uc hc h0 (andLeft (andRight hf))
  have hx := lambdaForward .erase upper left a i metadata uc xc hu h2 (andLeft (andRight (andRight hf)))
  have hl := lambdaForward .erase raw lower a i metadata child lc hc h1 (andLeft (andRight (andRight (andRight hf))))
  have hy := lambdaForward .erase lower right b j metadata lc yc hl h3 (andRight (andRight (andRight (andRight hf))))
  have hx' : Nonempty (Derivation body Delta (graph2 lambdaConstructor left metadata yc)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta _ left
      (Fin.cons metadata (Fin.cons xc Fin.elim0)) (Fin.cons metadata (Fin.cons yc Fin.elim0)) _ hx
    intro t
    refine Fin.cases ?_ (fun v => ?_) t
    · change Nonempty (Derivation body Delta (equal metadata metadata))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn metadata metadata)) from ⟨InternalTagArithmeticSupportProof.refl metadata⟩)
    · refine Fin.cases ?_ (fun e => Fin.elim0 e) v
      exact he
  have h := valueUnique lambdaConstructor left right (Fin.cons metadata (Fin.cons yc Fin.elim0)) hx' hy
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using h

theorem lambdaAt3 (raw metadata child a b i j upper lower left right uc lc xc : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph3 (fold .erase) uc b (suc (suc j)) child)))
    (h1 : Nonempty (Derivation body Delta (graph3 (fold .erase) lc a (suc i) child)))
    (h2 : Nonempty (Derivation body Delta (graph3 (fold .erase) xc a (suc i) uc)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases (fold .erase) b (suc j) lc _
  intro beta rho Theta yc hrho h3
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  have h2' := renameInto h2 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h0' h1' h2'
  simp only [sucRelabel] at h3
  exact lambdaAt4 (raw.relabel rho) (metadata.relabel rho) (child.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (uc.relabel rho) (lc.relabel rho) (xc.relabel rho) yc hi' hc' hf' h0' h1' h2' h3

theorem lambdaAt2 (raw metadata child a b i j upper lower left right uc lc : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph3 (fold .erase) uc b (suc (suc j)) child)))
    (h1 : Nonempty (Derivation body Delta (graph3 (fold .erase) lc a (suc i) child)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases (fold .erase) a (suc i) uc _
  intro beta rho Theta xc hrho h2
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h0' h1'
  simp only [sucRelabel] at h2
  exact lambdaAt3 (raw.relabel rho) (metadata.relabel rho) (child.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (uc.relabel rho) (lc.relabel rho) xc hi' hc' hf' h0' h1' h2

theorem lambdaAt1 (raw metadata child a b i j upper lower left right uc : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph3 (fold .erase) uc b (suc (suc j)) child)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases (fold .erase) a (suc i) child _
  intro beta rho Theta lc hrho h1
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h0'
  simp only [sucRelabel] at h1
  exact lambdaAt2 (raw.relabel rho) (metadata.relabel rho) (child.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (uc.relabel rho) lc hi' hc' hf' h0' h1

theorem lambdaAt0 (raw metadata child a b i j upper lower left right  : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases (fold .erase) b (suc (suc j)) child _
  intro beta rho Theta uc hrho h0
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [sucRelabel] at h0
  exact lambdaAt1 (raw.relabel rho) (metadata.relabel rho) (child.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) uc hi' hc' hf'  h0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLambdaProof
