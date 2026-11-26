module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.RawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransport (constant)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalDecodedDependencies
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem acceptedClosed (n : Nat) (node param left right out child a b : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph2 (dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child a b)))
    (ha : Nonempty (Derivation body Delta (graph2 (accepted n) (suc z) node param))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) a ⊓
      graph1 (OriginalCodeValidityGuard.check n) (numeral 1) b)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons node (Fin.cons param Fin.elim0)
  have hc := conjunctionRecover (sourceAccepted n) (targetAccepted n) xs ha
  have hl := unaryRecover (OriginalCodeValidityGuard.check n) source (numeral 1) left xs
    (andLeft hc) (OriginalDecodedDependencies.SupportProof.sourceAt node param left right hp)
  have hr := unaryRecover (OriginalCodeValidityGuard.check n) target (numeral 1) right xs
    (andRight hc) (OriginalDecodedDependencies.SupportProof.targetAt node param left right hp)
  have hx := successorBranchElim (accepted n) (constant 2 0) decodedCross out z xs ha hv
  have hd := binaryRecover NumericDependencyCross.rawDependencies source target out left right xs hx
    (OriginalDecodedDependencies.SupportProof.sourceAt node param left right hp)
    (OriginalDecodedDependencies.SupportProof.targetAt node param left right hp)
  exact RawProof.rawClosed left right out child a b hl hr hd hm hq

theorem atPair (n : Nat) (node param left right out child a b : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph2 (dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child a b))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) a ⊓
      graph1 (OriginalCodeValidityGuard.check n) (numeral 1) b)) := by
  apply formulaCases (graph2 (accepted n) (suc z) node param)
  · exact acceptedClosed n node param left right out child a b
      (withHyp hp _) (withHyp hv _) (withHyp hm _) (withHyp hq _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact OriginalDecodedDependencies.Proof.rejectedImpossible n node param out child _
      (withHyp hv _) (withHyp hm _) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem dependenciesClosed : Targets.InternalDependenciesClosed := by
  intro n body alpha Delta node param out child a b hv hm hq
  let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
  apply queryCases qs (Fin.cons node Fin.elim0) _
  intro beta j ys Theta hj hfields
  simp only [consTermRename,emptyRename] at hfields
  simp only [conjunctionRename,graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hp := reconstructPair (node.relabel j) (ys 0) (ys 1) (hfields 0) (hfields 1)
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  rw [graph2Rename] at hv'
  have hm' := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hq' := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  rw [graph2Rename] at hq'
  exact atPair n (node.relabel j) (param.relabel j) (ys 0) (ys 1) (out.relabel j)
    (child.relabel j) (a.relabel j) (b.relabel j) hp hv' hm' hq'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Proof
