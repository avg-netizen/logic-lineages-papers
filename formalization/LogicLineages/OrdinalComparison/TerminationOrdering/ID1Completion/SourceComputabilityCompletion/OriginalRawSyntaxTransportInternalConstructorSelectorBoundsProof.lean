module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalPairingSumBounds InternalPairingSumBoundsArithmeticProof
open InternalOriginalOrderSyntaxProof InternalUnpairReverseBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem numeralRelabel {beta : Type} (n : Nat) (j : alpha → beta) :
    (numeral n : OTerm alpha).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih => simpa only [numeral,sucRelabel] using congrArg suc ih

/-- The unary payload path is bounded without typing or constructor witnesses. -/
theorem unarySelectorsBound (tag : Nat) (htag : 1 ≤ tag) (raw child : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral tag) raw)))
    (hf : Nonempty (Derivation body Delta
      (graph1 (rightOf (rightOf (.projection 0))) child raw))) :
    Nonempty (Derivation body Delta (weakBound (suc child) raw)) := by
  apply programCases rawPayload (Fin.cons raw Fin.elim0) _
  intro beta j Theta payload hj hp
  simp only [weakRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have ht' := renameInto ht j Theta hj
  have hf' := renameInto hf j Theta hj
  simp only [graph1Rename,numeralRelabel] at ht' hf'
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hpv := unaryValue InternalUnpair.right (.projection 0) payload (raw.relabel j) xs hp
    (projectionValue 0 xs)
  have hc := unaryRecover InternalUnpair.right (rightOf (.projection 0)) (child.relabel j) payload xs hf' hpv
  exact taggedUnaryBound tag htag (raw.relabel j) payload (child.relabel j)
    (reconstructPair (raw.relabel j) (numeral tag) payload ht' hp)
    (rightBound payload (child.relabel j) hc)

/-- Application/cons child paths pay the exact two-child sum from the raw tag. -/
theorem binarySelectorsBound (tag : Nat) (htag : 2 ≤ tag) (raw first second : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral tag) raw)))
    (hf : Nonempty (Derivation body Delta
      (graph1 (leftOf (rightOf (rightOf (.projection 0)))) first raw)))
    (hs : Nonempty (Derivation body Delta
      (graph1 (rightOf (rightOf (rightOf (.projection 0)))) second raw))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  let qs : Fin 2 → Program 1 := ![rightOf (.projection 0),rightOf (rightOf (.projection 0))]
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [weakRename,childFuelSum,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have ht' := renameInto ht j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph1Rename,numeralRelabel] at ht' hf' hs'
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xs
    (hq 0) (projectionValue 0 xs)
  have hc := unaryRecover InternalUnpair.right (rightOf (.projection 0)) (ys 1) (ys 0) xs (hq 1) (hq 0)
  have hl := unaryRecover InternalUnpair.left (rightOf (rightOf (.projection 0)))
    (first.relabel j) (ys 1) xs hf' (hq 1)
  have hr := unaryRecover InternalUnpair.right (rightOf (rightOf (.projection 0)))
    (second.relabel j) (ys 1) xs hs' (hq 1)
  have hsum := pairSum (ys 1) (first.relabel j) (second.relabel j)
    (reconstructPair (ys 1) (first.relabel j) (second.relabel j) hl hr)
  exact taggedBinaryBound tag htag (raw.relabel j) (ys 0) (first.relabel j) (second.relabel j)
    (reconstructPair (raw.relabel j) (numeral tag) (ys 0) ht' hp)
    (weakTrans _ (ys 1) (ys 0) hsum (rightBound (ys 0) (ys 1) hc))

/-- Numbered base and extras are the two traversed children. The extra-type
list remains metadata between them and is only discarded in this lower bound. -/
theorem numberedSelectorsBound (raw first second : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hf : Nonempty (Derivation body Delta
      (graph1 (leftOf (rightOf (rightOf (rightOf (rightOf (.projection 0)))))) first raw)))
    (hs : Nonempty (Derivation body Delta
      (graph1 (rightOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0))))))) second raw))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  let qs : Fin 3 → Program 1 := ![rightOf (.projection 0),
    rightOf (rightOf (rightOf (rightOf (.projection 0)))),
    rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0)))))]
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [weakRename,childFuelSum,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have ht' := renameInto ht j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph1Rename,numeralRelabel] at ht' hf' hs'
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xs
    (hq 0) (projectionValue 0 xs)
  have hcontainer := pathBound [true,true,true] (rightOf (.projection 0)) (ys 0) (ys 1) xs (hq 0) (hq 1)
  have hl := unaryRecover InternalUnpair.left (rightOf (rightOf (rightOf (rightOf (.projection 0)))))
    (first.relabel j) (ys 1) xs hf' (hq 1)
  have hr := unaryRecover InternalUnpair.right (rightOf (rightOf (rightOf (rightOf (.projection 0)))))
    (ys 2) (ys 1) xs (hq 2) (hq 1)
  have he := unaryRecover InternalUnpair.right (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0))))))
    (second.relabel j) (ys 2) xs hs' (hq 2)
  have hsum := pairSum (ys 1) (first.relabel j) (ys 2)
    (reconstructPair (ys 1) (first.relabel j) (ys 2) hl hr)
  have hshort := addWeakLeft (first.relabel j) (second.relabel j) (ys 2)
    (rightBound (ys 2) (second.relabel j) he)
  exact taggedBinaryBound 5 (by decide) (raw.relabel j) (ys 0) (first.relabel j) (second.relabel j)
    (reconstructPair (raw.relabel j) (numeral 5) (ys 0) ht' hp)
    (weakTrans _ (ys 1) (ys 0) (weakTrans _ _ _ hshort hsum) hcontainer)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
