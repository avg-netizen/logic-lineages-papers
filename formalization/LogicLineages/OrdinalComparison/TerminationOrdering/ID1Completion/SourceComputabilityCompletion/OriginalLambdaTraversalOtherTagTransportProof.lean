module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOtherTagTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Transfer the actual conditional graph using shared values of all three
arguments. This works for arbitrary control/output values, not only booleans. -/
theorem branchTransfer {n : Nat} (control a b : Program n)
    (out c av bv : OTerm alpha) (xs ys : Fin n → OTerm alpha)
    (hcx : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hax : Nonempty (Derivation body Delta (programGraph a av xs)))
    (hbx : Nonempty (Derivation body Delta (programGraph b bv xs)))
    (hcy : Nonempty (Derivation body Delta (programGraph control c ys)))
    (hay : Nonempty (Derivation body Delta (programGraph a av ys)))
    (hby : Nonempty (Derivation body Delta (programGraph b bv ys)))
    (h : Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control a b) out xs))) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control a b) out ys)) := by
  have hc : Nonempty (Derivation body Delta
      (programGraph GorbowPRInternalControl.conditional out
        (Fin.cons c (Fin.cons av (Fin.cons bv Fin.elim0))))) := by
    apply compositionRecover GorbowPRInternalControl.conditional
      (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs
      (Fin.cons c (Fin.cons av (Fin.cons bv Fin.elim0))) h
    intro i
    exact Fin.cases hcx (Fin.cases hax (Fin.cases hbx (fun j => Fin.elim0 j))) i
  exact branchValue control a b out c av bv ys hcy hay hby hc

/-- The exact otherTag AST depends only on the original raw root tag.
Both nested branch controls and constants are transported internally. -/
theorem atSameTag (source target tag out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag source)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag tag target)))
    (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag out source))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag out target)) := by
  let tagP := OriginalLambdaTraversal.rawTag
  let test2 := InternalApplicationStepPeel.same tagP (two 1)
  let test1 := OriginalHereditaryValidity.exactOne tagP
  let inner := InternalAcceptance.branch test1
    (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
  let qs : Fin 3 → Program 1 := ![test2,test1,inner]
  apply InternalApplicationStepPeelSupportProof.queryCases qs (Fin.cons source Fin.elim0) _
  intro beta j codes Theta hj hq
  rw [graph1Rename]
  have hs' := renameInto hs j Theta hj
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph1Rename] at hs' ht' ho'
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 1 → OTerm beta := Fin.cons (source.relabel j) Fin.elim0
  let ys : Fin 1 → OTerm beta := Fin.cons (target.relabel j) Fin.elim0
  have h2x : Nonempty (Derivation body Theta (programGraph test2 (codes 0) xs)) := hq 0
  have h1x : Nonempty (Derivation body Theta (programGraph test1 (codes 1) xs)) := hq 1
  have hix : Nonempty (Derivation body Theta (programGraph inner (codes 2) xs)) := hq 2
  have h2 := binaryRecover InternalEqualityTest.equalityTest tagP (two 1)
    (codes 0) (tag.relabel j) (suc (suc z)) xs h2x hs' (twoValue xs)
  have h1 := binaryRecover InternalEqualityTest.equalityTest tagP (InternalLessThan.constantOne 1)
    (codes 1) (tag.relabel j) (suc z) xs h1x hs' (InternalLessThanSupportProof.oneConstantValue xs)
  have h2y : Nonempty (Derivation body Theta (programGraph test2 (codes 0) ys)) :=
    binaryValue InternalEqualityTest.equalityTest tagP (two 1)
      (codes 0) (tag.relabel j) (suc (suc z)) ys h2 ht' (twoValue ys)
  have h1y : Nonempty (Derivation body Theta (programGraph test1 (codes 1) ys)) :=
    binaryValue InternalEqualityTest.equalityTest tagP (InternalLessThan.constantOne 1)
      (codes 1) (tag.relabel j) (suc z) ys h1 ht' (InternalLessThanSupportProof.oneConstantValue ys)
  have hiy := branchTransfer test1 (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
    (codes 2) (codes 1) (suc z) z xs ys h1x
    (InternalLessThanSupportProof.oneConstantValue xs) (InternalLessThanSupportProof.zeroConstantValue xs)
    h1y (InternalLessThanSupportProof.oneConstantValue ys) (InternalLessThanSupportProof.zeroConstantValue ys) hix
  exact branchTransfer test2 inner (InternalAcceptance.constantZero 1)
    (out.relabel j) (codes 0) (codes 2) z xs ys h2x hix
    (InternalLessThanSupportProof.zeroConstantValue xs) h2y hiy
    (InternalLessThanSupportProof.zeroConstantValue ys) ho'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOtherTagTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOtherTagTransportProof
