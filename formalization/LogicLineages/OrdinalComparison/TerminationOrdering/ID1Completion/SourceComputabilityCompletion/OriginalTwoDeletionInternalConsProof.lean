module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalConsProof
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
open OriginalRawSyntaxTransportInternalFoldConsProof
open OriginalRawSyntaxTransportInternalCancellationNumberedProof (tupleSixRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consAt4 (raw metadata first second a b i j upper lower left right u1 u2 l1 l2 x1 x2 y1 y2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h00 : Nonempty (Derivation body Delta (graph3 (fold .erase) u1 b (suc j) first)))
    (h01 : Nonempty (Derivation body Delta (graph3 (fold .erase) u2 b (suc j) second)))
    (h10 : Nonempty (Derivation body Delta (graph3 (fold .erase) l1 a i first)))
    (h11 : Nonempty (Derivation body Delta (graph3 (fold .erase) l2 a i second)))
    (h20 : Nonempty (Derivation body Delta (graph3 (fold .erase) x1 a i u1)))
    (h21 : Nonempty (Derivation body Delta (graph3 (fold .erase) x2 a i u2)))
    (h30 : Nonempty (Derivation body Delta (graph3 (fold .erase) y1 b j l1)))
    (h31 : Nonempty (Derivation body Delta (graph3 (fold .erase) y2 b j l2)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  have hshape := consFields raw metadata first second hc
  have hsmall := binaryChildrenStrict raw first second (andLeft hshape) (andLeft (andRight hshape)) (andRight (andRight hshape))
  have he0 := belowRawApply (fold .erase) raw first a b i j u1 l1 x1 y1 hi (andLeft hsmall)
    (andIntro (andLeft hf) (andIntro h00 (andIntro h20 (andIntro h10 h30))))
  have he1 := belowRawApply (fold .erase) raw second a b i j u2 l2 x2 y2 hi (andRight hsmall)
    (andIntro (andLeft hf) (andIntro h01 (andIntro h21 (andIntro h11 h31))))
  have hu := consForward .erase raw upper b (suc j) metadata first second u1 u2 hc h00 h01 (andLeft (andRight hf))
  have hx := consForward .erase upper left a i metadata u1 u2 x1 x2 hu h20 h21 (andLeft (andRight (andRight hf)))
  have hl := consForward .erase raw lower a i metadata first second l1 l2 hc h10 h11 (andLeft (andRight (andRight (andRight hf))))
  have hy := consForward .erase lower right b j metadata l1 l2 y1 y2 hl h30 h31 (andRight (andRight (andRight (andRight hf))))
  have hx' : Nonempty (Derivation body Delta (graph3 consConstructor left metadata y1 y2)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta _ left
      (![metadata,x1,x2]) (![metadata,y1,y2]) _ hx
    intro t
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun e => Fin.elim0 e))) t
    · change Nonempty (Derivation body Delta (equal metadata metadata))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn metadata metadata)) from ⟨InternalTagArithmeticSupportProof.refl metadata⟩)
    · exact he0
    · exact he1
  have h := valueUnique consConstructor left right (![metadata,y1,y2]) hx' hy
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using h

theorem consAt3 (raw metadata first second a b i j upper lower left right u1 u2 l1 l2 x1 x2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h00 : Nonempty (Derivation body Delta (graph3 (fold .erase) u1 b (suc j) first)))
    (h01 : Nonempty (Derivation body Delta (graph3 (fold .erase) u2 b (suc j) second)))
    (h10 : Nonempty (Derivation body Delta (graph3 (fold .erase) l1 a i first)))
    (h11 : Nonempty (Derivation body Delta (graph3 (fold .erase) l2 a i second)))
    (h20 : Nonempty (Derivation body Delta (graph3 (fold .erase) x1 a i u1)))
    (h21 : Nonempty (Derivation body Delta (graph3 (fold .erase) x2 a i u2)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply binaryChildCases (fold .erase) b j l1 l2 _
  intro beta rho Theta y1 y2 hrho h30 h31
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h00' := renameInto h00 rho Theta hrho
  have h01' := renameInto h01 rho Theta hrho
  have h10' := renameInto h10 rho Theta hrho
  have h11' := renameInto h11 rho Theta hrho
  have h20' := renameInto h20 rho Theta hrho
  have h21' := renameInto h21 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01' h10' h11' h20' h21'
  exact consAt4 (raw.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) (l1.relabel rho) (l2.relabel rho) (x1.relabel rho) (x2.relabel rho) y1 y2 hi' hc' hf' h00' h01' h10' h11' h20' h21' h30 h31

theorem consAt2 (raw metadata first second a b i j upper lower left right u1 u2 l1 l2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h00 : Nonempty (Derivation body Delta (graph3 (fold .erase) u1 b (suc j) first)))
    (h01 : Nonempty (Derivation body Delta (graph3 (fold .erase) u2 b (suc j) second)))
    (h10 : Nonempty (Derivation body Delta (graph3 (fold .erase) l1 a i first)))
    (h11 : Nonempty (Derivation body Delta (graph3 (fold .erase) l2 a i second)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply binaryChildCases (fold .erase) a i u1 u2 _
  intro beta rho Theta x1 x2 hrho h20 h21
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h00' := renameInto h00 rho Theta hrho
  have h01' := renameInto h01 rho Theta hrho
  have h10' := renameInto h10 rho Theta hrho
  have h11' := renameInto h11 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01' h10' h11'
  exact consAt3 (raw.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) (l1.relabel rho) (l2.relabel rho) x1 x2 hi' hc' hf' h00' h01' h10' h11' h20 h21

theorem consAt1 (raw metadata first second a b i j upper lower left right u1 u2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    (h00 : Nonempty (Derivation body Delta (graph3 (fold .erase) u1 b (suc j) first)))
    (h01 : Nonempty (Derivation body Delta (graph3 (fold .erase) u2 b (suc j) second)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply binaryChildCases (fold .erase) a i first second _
  intro beta rho Theta l1 l2 hrho h10 h11
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have h00' := renameInto h00 rho Theta hrho
  have h01' := renameInto h01 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01'
  exact consAt2 (raw.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) l1 l2 hi' hc' hf' h00' h01' h10 h11

theorem consAt0 (raw metadata first second a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply binaryChildCases (fold .erase) b (suc j) first second _
  intro beta rho Theta u1 u2 hrho h00 h01
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [sucRelabel] at h00 h01
  exact consAt1 (raw.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) u1 u2 hi' hc' hf' h00 h01


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalConsProof
