module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalNumberedProof
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
open OriginalRawSyntaxTransportInternalFoldNumberedProof
open OriginalRawSyntaxTransportInternalCancellationNumberedProof (tupleSixRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem numberedAt4 (raw label head tau types first second a b i j upper lower left right u1 u2 l1 l2 x1 x2 y1 y2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,first,types,second])))
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
  have hshape := numberedFields raw label head tau first types second hc
  have hsmall := binaryChildrenStrict raw first second (andLeft hshape) (andLeft (andRight hshape)) (andRight (andRight hshape))
  have he0 := belowRawApply (fold .erase) raw first a b i j u1 l1 x1 y1 hi (andLeft hsmall)
    (andIntro (andLeft hf) (andIntro h00 (andIntro h20 (andIntro h10 h30))))
  have he1 := belowRawApply (fold .erase) raw second a b i j u2 l2 x2 y2 hi (andRight hsmall)
    (andIntro (andLeft hf) (andIntro h01 (andIntro h21 (andIntro h11 h31))))
  have hu := numberedForward .erase raw upper b (suc j) label head tau first types second u1 u2 hc h00 h01 (andLeft (andRight hf))
  have hx := numberedForward .erase upper left a i label head tau u1 types u2 x1 x2 hu h20 h21 (andLeft (andRight (andRight hf)))
  have hl := numberedForward .erase raw lower a i label head tau first types second l1 l2 hc h10 h11 (andLeft (andRight (andRight (andRight hf))))
  have hy := numberedForward .erase lower right b j label head tau l1 types l2 y1 y2 hl h30 h31 (andRight (andRight (andRight (andRight hf))))
  have hx' : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,tau,y1,types,y2])) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 6 Delta _ left
      (![label,head,tau,x1,types,x2]) (![label,head,tau,y1,types,y2]) _ hx
    intro t
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun e => Fin.elim0 e)))))) t
    · change Nonempty (Derivation body Delta (equal label label))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn label label)) from ⟨InternalTagArithmeticSupportProof.refl label⟩)
    · change Nonempty (Derivation body Delta (equal head head))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn head head)) from ⟨InternalTagArithmeticSupportProof.refl head⟩)
    · change Nonempty (Derivation body Delta (equal tau tau))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn tau tau)) from ⟨InternalTagArithmeticSupportProof.refl tau⟩)
    · exact he0
    · change Nonempty (Derivation body Delta (equal types types))
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using
        (show Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn types types)) from ⟨InternalTagArithmeticSupportProof.refl types⟩)
    · exact he1
  have h := valueUnique numberedConstructor left right (![label,head,tau,y1,types,y2]) hx' hy
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using h

theorem numberedAt3 (raw label head tau types first second a b i j upper lower left right u1 u2 l1 l2 x1 x2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,first,types,second])))
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
  simp only [programRename,tupleSixRename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01' h10' h11' h20' h21'
  exact numberedAt4 (raw.relabel rho) (label.relabel rho) (head.relabel rho) (tau.relabel rho) (types.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) (l1.relabel rho) (l2.relabel rho) (x1.relabel rho) (x2.relabel rho) y1 y2 hi' hc' hf' h00' h01' h10' h11' h20' h21' h30 h31

theorem numberedAt2 (raw label head tau types first second a b i j upper lower left right u1 u2 l1 l2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,first,types,second])))
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
  simp only [programRename,tupleSixRename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01' h10' h11'
  exact numberedAt3 (raw.relabel rho) (label.relabel rho) (head.relabel rho) (tau.relabel rho) (types.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) (l1.relabel rho) (l2.relabel rho) x1 x2 hi' hc' hf' h00' h01' h10' h11' h20 h21

theorem numberedAt1 (raw label head tau types first second a b i j upper lower left right u1 u2 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,first,types,second])))
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
  simp only [programRename,tupleSixRename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [graph3Rename,sucRelabel] at h00' h01'
  exact numberedAt2 (raw.relabel rho) (label.relabel rho) (head.relabel rho) (tau.relabel rho) (types.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (u1.relabel rho) (u2.relabel rho) l1 l2 hi' hc' hf' h00' h01' h10 h11

theorem numberedAt0 (raw label head tau types first second a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,first,types,second])))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  apply binaryChildCases (fold .erase) b (suc j) first second _
  intro beta rho Theta u1 u2 hrho h00 h01
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [programRename,tupleSixRename] at hc'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  simp only [sucRelabel] at h00 h01
  exact numberedAt1 (raw.relabel rho) (label.relabel rho) (head.relabel rho) (tau.relabel rho) (types.relabel rho) (first.relabel rho) (second.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) u1 u2 hi' hc' hf' h00 h01


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalNumberedProof
