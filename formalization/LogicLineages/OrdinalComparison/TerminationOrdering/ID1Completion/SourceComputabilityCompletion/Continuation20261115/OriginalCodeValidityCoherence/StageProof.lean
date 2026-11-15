module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.TableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.StageProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalSquareRootArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fuelNonzero (raw fuel : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel))) :
    Nonempty (Derivation body Delta (eqn fuel z).not) := by
  let A := eqn fuel z
  obtain ⟨hf⟩ := hf
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
    (body := body) (Gamma := A :: Delta) raw
  have hz := orderRight raw (Derivation.hypothesis List.mem_cons_self)
    (InternalBetaTotalityProof.addHyp hf A)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hz)⟩

theorem childFuel (child raw predecessor : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hf : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc predecessor)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child predecessor)) :=
  strictWeakTrans child raw predecessor hc hf

theorem childBound (child raw bound : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child (suc bound))) :=
  strictTrans child raw (suc bound) hc hb

theorem stageCases (n : Nat) (raw fuel bound table : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel)))
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) table fuel bound)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (predecessor previous : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (InternalLessThan.strictLess (raw.relabel j) (suc predecessor))) →
      Nonempty (Derivation body Theta
        (graph2 (OriginalCodeDecoderTable.tableProgram n) previous predecessor (bound.relabel j))) →
      Nonempty (Derivation body Theta
        (graph2 (OriginalCodeDecoderTable.nextRow n) (table.relabel j) (bound.relabel j) previous)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let pred : Program 2 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => .projection 0)
  let old : Program 2 := .composition (OriginalCodeDecoderTable.tableProgram n) ![pred,.projection 1]
  let qs : Fin 2 → Program 2 := ![pred,old]
  let xs : Fin 2 → OTerm alpha := Fin.cons fuel (Fin.cons bound Fin.elim0)
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (fuel.relabel j) (Fin.cons (bound.relabel j) Fin.elim0)
  have hp := unaryRecover InternalEqualityTest.predecessor (.projection 0) (ys 0) (fuel.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have ho := binaryRecover (OriginalCodeDecoderTable.tableProgram n) pred (.projection 1)
    (ys 1) (ys 0) (bound.relabel j) xx (hq 1) (hq 0) (projectionValue 1 xx)
  have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [InternalLessThan.strictLess, InternalOriginalOrderSyntaxProof.orderRename] at hf'
  have he := InternalListCodecDecompositionSupportProof.predecessorAtNonzero (fuel.relabel j) (ys 0)
    (fuelNonzero (raw.relabel j) (fuel.relabel j) hf') hp
  have ht' := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph2Rename] at ht'
  have hnext := headTransport (OriginalCodeDecoderTable.tableProgram n) (table.relabel j)
    (fuel.relabel j) (suc (ys 0)) (Fin.cons (bound.relabel j) Fin.elim0) he ht'
  have hrow := OriginalCodeValidityGuard.TableSupportProof.nextRowRecover n (ys 0) (bound.relabel j)
    (ys 1) (table.relabel j) ho hnext
  obtain ⟨he⟩ := he
  obtain ⟨hf'⟩ := hf'
  exact next beta j Theta (ys 0) (ys 1) hj ⟨orderRight (raw.relabel j) he hf'⟩ ho hrow
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.StageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.StageProof
