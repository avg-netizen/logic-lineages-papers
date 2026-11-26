module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLengthCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem headZero : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode (z : OTerm alpha) z)) :=
  unaryValue InternalUnpair.left InternalEqualityTest.predecessor z z (Fin.cons z Fin.elim0)
    (pairLeft z z z InternalApplicationValidityStackAppendTransitionProof.pairZero)
    InternalEqualityTestPredecessorProof.predecessorZero

theorem tailZero : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode (z : OTerm alpha) z)) :=
  unaryValue InternalUnpair.right InternalEqualityTest.predecessor z z (Fin.cons z Fin.elim0)
    (pairRight z z z InternalApplicationValidityStackAppendTransitionProof.pairZero)
    InternalEqualityTestPredecessorProof.predecessorZero

theorem lookupNilZero : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (z : OTerm alpha) z z)) :=
  InternalRawListRecursionSupportProof.lookupValue z z z z (InternalRawListRecursionSupportProof.dropZero z) headZero

theorem lookupNilOne : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (z : OTerm alpha) (suc z) z)) :=
  InternalRawListRecursionSupportProof.lookupValue z (suc z) z z
    (InternalRawListRecursionSupportProof.dropNext z z z z (InternalRawListRecursionSupportProof.dropZero z) tailZero) headZero

theorem singleton (row first : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc z) row)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row))) :
    Nonempty (Derivation body Delta (consGraph row first z)) := by
  apply AdmittedLengthCasesProof.singletonCases row _ hl
  intro beta j Theta head hj hc
  simp only [consGraphRename,zRelabel]
  have hf' := renameInto hf j Theta hj
  simp only [graph2Rename,zRelabel] at hf'
  have he := valueUnique InternalRawListRecursion.lookup head (first.relabel j)
    (Fin.cons z (Fin.cons (row.relabel j) Fin.elim0))
    (OriginalAllPositionContextDeleteBaseProof.lookupZero (row.relabel j) head z hc) hf'
  exact headTransport InternalListCodec.consCode (row.relabel j) head (first.relabel j) (Fin.cons z Fin.elim0) he hc

theorem secondDefault (row first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph row first z)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row))) :
    Nonempty (Derivation body Delta (eqn second z)) := by
  obtain ⟨law⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff row first z z second hc
  have hz : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second z z)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice hs)⟩
  exact valueUnique InternalRawListRecursion.lookup second z (Fin.cons z (Fin.cons z Fin.elim0)) hz lookupNilZero

theorem binaryCases (row first second : OTerm alpha) (psi : Formula alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc (suc z)) row)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tail : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (row.relabel j) (first.relabel j) tail)) →
      Nonempty (Derivation body Theta (consGraph tail (second.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply AdmittedLengthCasesProof.successorCases row (suc z) psi hl
  intro beta j Theta head tail hj hc ht
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hf' hs'
  simp only [sucRelabel,zRelabel] at ht
  have he := valueUnique InternalRawListRecursion.lookup head (first.relabel j)
    (Fin.cons z (Fin.cons (row.relabel j) Fin.elim0))
    (OriginalAllPositionContextDeleteBaseProof.lookupZero (row.relabel j) head tail hc) hf'
  have hrow := headTransport InternalListCodec.consCode (row.relabel j) head (first.relabel j) (Fin.cons tail Fin.elim0) he hc
  obtain ⟨law⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff (row.relabel j) (first.relabel j) tail z (second.relabel j) hrow
  have hsecond : Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup (second.relabel j) z tail)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice hs')⟩
  exact next beta j Theta tail hj hrow (singleton tail (second.relabel j) ht hsecond)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
