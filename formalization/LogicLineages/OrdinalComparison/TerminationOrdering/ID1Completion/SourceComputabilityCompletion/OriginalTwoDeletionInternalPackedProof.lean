module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof hiding andIntro andLeft andRight
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof
open OriginalTwoDeletionInternalDefinitions OriginalTwoDeletionInternalSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open InternalAcceptanceSupportProof (programCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem packedAt5 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau raw uc lc xc : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw packed)))
    (h2 : Nonempty (Derivation body Delta (graph3 eraseRaw uc b (suc j) raw)))
    (h3 : Nonempty (Derivation body Delta (graph3 eraseRaw lc a i raw)))
    (h4 : Nonempty (Derivation body Delta (graph3 eraseRaw xc a i uc)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases eraseRaw b j lc _
  intro beta rho Theta yc hrho h5
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  have h2' := renameInto h2 rho Theta hrho
  have h3' := renameInto h3 rho Theta hrho
  have h4' := renameInto h4 rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph1Rename,graph3Rename,sucRelabel] at h0' h1' h2' h3' h4'
  exact packedAt6 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (tau.relabel rho) (raw.relabel rho) (uc.relabel rho) (lc.relabel rho) (xc.relabel rho) yc hf' h0' h1' h2' h3' h4' h5

theorem packedAt4 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau raw uc lc : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw packed)))
    (h2 : Nonempty (Derivation body Delta (graph3 eraseRaw uc b (suc j) raw)))
    (h3 : Nonempty (Derivation body Delta (graph3 eraseRaw lc a i raw)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases eraseRaw a i uc _
  intro beta rho Theta xc hrho h4
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  have h2' := renameInto h2 rho Theta hrho
  have h3' := renameInto h3 rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph1Rename,graph3Rename,sucRelabel] at h0' h1' h2' h3'
  exact packedAt5 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (tau.relabel rho) (raw.relabel rho) (uc.relabel rho) (lc.relabel rho) xc hf' h0' h1' h2' h3' h4

theorem packedAt3 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau raw uc : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw packed)))
    (h2 : Nonempty (Derivation body Delta (graph3 eraseRaw uc b (suc j) raw)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases eraseRaw a i raw _
  intro beta rho Theta lc hrho h3
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  have h2' := renameInto h2 rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph1Rename,graph3Rename,sucRelabel] at h0' h1' h2'
  exact packedAt4 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (tau.relabel rho) (raw.relabel rho) (uc.relabel rho) lc hf' h0' h1' h2' h3

theorem packedAt2 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau raw : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw packed)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply ternaryCases eraseRaw b (suc j) raw _
  intro beta rho Theta uc hrho h2
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  have h1' := renameInto h1 rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph1Rename,graph3Rename,sucRelabel] at h0' h1'
  simp only [consTermRename,emptyRename,sucRelabel] at h2
  exact packedAt3 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (tau.relabel rho) (raw.relabel rho) uc hf' h0' h1' h2

theorem packedAt1 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right tau : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tau packed)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply programCases InternalUnpair.right (Fin.cons packed Fin.elim0) _
  intro beta rho Theta raw hrho h1
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  have h0' := renameInto h0 rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph1Rename,graph3Rename,sucRelabel] at h0'
  simp only [consTermRename,emptyRename,sucRelabel] at h1
  exact packedAt2 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (tau.relabel rho) raw hf' h0' h1

theorem packedAt0 (supply : OriginalTwoDeletionInternalTargets.RawCommutation) (packed a b i j upper lower left right  : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields erasePackedRaw packed a b i j upper lower left right)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply programCases InternalUnpair.left (Fin.cons packed Fin.elim0) _
  intro beta rho Theta tau hrho h0
  rw [equalRename]
  have hf' := renameInto hf rho Theta hrho
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [consTermRename,emptyRename,sucRelabel] at h0
  exact packedAt1 supply (packed.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) tau hf'  h0

theorem packedFromRaw (supply : OriginalTwoDeletionInternalTargets.RawCommutation) :
    OriginalTwoDeletionInternalTargets.PackedCommutation := by
  intro body alpha Delta packed a b i j upper lower left right
  let A := fields erasePackedRaw packed a b i j upper lower left right
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := packedAt0 supply packed a b i j upper lower left right ha
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalPackedProof
