module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLengthCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryInputs (P : Program 2) (out a b a' b' : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (eqn a a')))
 (hb : Nonempty (Derivation body Delta (eqn b b')))
 (hp : Nonempty (Derivation body Delta (graph2 P out a b))) :
 Nonempty (Derivation body Delta (graph2 P out a' b')) := by
 apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula P)
   out (Fin.cons a (Fin.cons b Fin.elim0)) (Fin.cons a' (Fin.cons b' Fin.elim0)) _ hp
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
 · rw [InternalSourceInversionSupportProof.onEquality]; exact ha
 · rw [InternalSourceInversionSupportProof.onEquality]; exact hb

theorem tailLength (code head tail count : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph code head tail)))
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc count) code))) :
    Nonempty (Derivation body Delta (lengthGraph count tail)) := by
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta j Theta d hj hd
  rw [lengthRename]
  have hc' := renameInto hc j Theta hj
  have hl' := renameInto hl j Theta hj
  simp only [consGraphRename,lengthRename,sucRelabel] at hc' hl'
  simp only [consTermRename,emptyRename] at hd
  obtain ⟨he⟩ := lengthConsRecover (code.relabel j) (head.relabel j) (tail.relabel j)
    (suc (count.relabel j)) d hc' hl' hd
  exact outputTransport length d (count.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)
    ⟨symm (cancelSuc he)⟩ hd

theorem successorCases (code count : OTerm alpha) (psi : Formula alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc count) code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (head tail : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (code.relabel j) head tail)) →
      Nonempty (Derivation body Theta (lengthGraph (count.relabel j) tail)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have hn : Nonempty (Derivation body Delta (eqn code z).not) := by
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have hl' : Nonempty (Derivation body (eqn code z :: Delta) (lengthGraph (suc count) code)) :=
      ⟨Derivation.weakening (fun f hf => List.mem_cons_of_mem _ hf) (Classical.choice hl)⟩
    have hz := headTransport length (suc count) code z Fin.elim0
      ⟨Derivation.hypothesis List.mem_cons_self⟩ hl'
    exact sucNeZeroApply (Classical.choice (lengthNilRecover (suc count) hz))
  apply nonzeroCases code psi hn
  intro beta j Theta head tail hj hc
  have hl' := renameInto hl j Theta hj
  simp only [lengthRename,sucRelabel] at hl'
  exact next beta j Theta head tail hj hc (tailLength (code.relabel j) head tail (count.relabel j) hc hl')

theorem singletonCases (code : OTerm alpha) (psi : Formula alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc z) code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (head : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (code.relabel j) head z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply successorCases code z psi hl
  intro beta j Theta head tail hj hc ht
  rw [zRelabel] at ht
  exact next beta j Theta head hj
    (binaryInputs InternalListCodec.consCode (code.relabel j) head tail head z
      ⟨refl head⟩ (lengthZeroRecover tail ht) hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLengthCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLengthCasesProof
