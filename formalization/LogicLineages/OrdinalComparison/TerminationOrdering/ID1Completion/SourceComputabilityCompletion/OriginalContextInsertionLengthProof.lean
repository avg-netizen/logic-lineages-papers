module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalControlGraphChoiceProof
open InternalControlGraphSupportProof InternalRawListRecursionSyntaxProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion OriginalContextInsertionSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem lengthZero : Nonempty (Derivation body Gamma (lengthGraph (z : OTerm alpha) z)) :=
  InternalRawListRecursionProof.nilValue InternalRawListRecursion.zero lengthStep z Fin.elim0
    (constantZero Fin.elim0)

 theorem lengthStepValue (head count : OTerm alpha) :
    Nonempty (Derivation body Gamma (programGraph lengthStep (suc count)
      (Fin.cons head (Fin.cons count Fin.elim0)))) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection 1) (suc count)
    (Fin.cons head (Fin.cons count Fin.elim0)) (Fin.cons count Fin.elim0)
    (InternalControlGraphSupportProof.successorValue (Fin.cons count Fin.elim0))
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 (Fin.cons head (Fin.cons count Fin.elim0))

 theorem lengthCons (code head tail count : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count tail))) :
    Nonempty (Derivation body Gamma (lengthGraph (suc count) code)) :=
  InternalRawListRecursionProof.consValue InternalRawListRecursion.zero lengthStep
    code head tail count (suc count) Fin.elim0 hc hl (lengthStepValue head count)

 theorem lengthNilRecover (count : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count z))) :
    Nonempty (Derivation body Gamma (eqn count z)) :=
  valueUnique length count z (Fin.cons z Fin.elim0) hl lengthZero

 theorem lengthConsRecover (code head tail count tailCount : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count code)))
    (ht : Nonempty (Derivation body Gamma (lengthGraph tailCount tail))) :
    Nonempty (Derivation body Gamma (eqn count (suc tailCount))) :=
  valueUnique length count (suc tailCount) (Fin.cons code Fin.elim0) hl
    (lengthCons code head tail tailCount hc ht)

/-- Recover an original cons decomposition at a nonzero raw list code by
original head/tail totality and inverse laws, not by native decoding. -/
 theorem nonzeroCases (code : OTerm alpha) (psi : Formula alpha)
    (hn : Nonempty (Derivation body Gamma (eqn code z).not))
    (next : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (head tail : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (consGraph (code.relabel j) head tail)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases InternalListCodec.headCode (Fin.cons code Fin.elim0) _
  intro beta j Delta head hj hh
  apply programCases InternalListCodec.tailCode (Fin.cons (code.relabel j) Fin.elim0) _
  intro beta' k Theta tail hk ht
  have hn' := renameInto (renameInto hn j Delta hj) k Theta hk
  simp only [nonzeroRename] at hn'
  have hh' := renameInto hh k Theta hk
  simp only [programRename,consTermRename,emptyRename] at hh'
  simp only [consTermRename,emptyRename] at ht
  have hc := reconstructNonzero ((code.relabel j).relabel k) (head.relabel k) tail hn' hh' ht
  have h := next beta' (k ∘ j) Theta (head.relabel k) tail
    (fun p hp => by simpa only [formulaRelabelComposition] using hk _ (hj p hp))
    (by simpa only [Term.relabel_relabel] using hc)
  simpa only [formulaRelabelComposition] using h

 theorem listCases (code : OTerm alpha) (psi : Formula alpha)
    (hz : Nonempty (Derivation body (eqn code z :: Gamma) psi))
    (next : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (head tail : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (consGraph (code.relabel j) head tail)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := nonzeroCases (Gamma := (eqn code z).not :: Gamma) code psi
    ⟨Derivation.hypothesis List.mem_cons_self⟩
    (fun beta j Delta head tail hj hc => next beta j Delta head tail
      (fun p hp => hj p (List.mem_cons_of_mem _ hp)) hc)
  exact ⟨disjunctionElimination (excludedMiddle (eqn code z))
    (Derivation.implicationIntroduction hz) (Derivation.implicationIntroduction hs)⟩

 theorem lengthZeroRecover (code : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph z code))) :
    Nonempty (Derivation body Gamma (eqn code z)) := by
  apply listCases code _ ⟨Derivation.hypothesis List.mem_cons_self⟩
  intro beta j Delta head tail hj hc
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta' k Theta count hk ht
  have hl' := renameInto (renameInto hl j Delta hj) k Theta hk
  simp only [lengthRename,zRelabel] at hl'
  have hc' := renameInto hc k Theta hk
  rw [consGraphRename] at hc'
  simp only [consTermRename,emptyRename] at ht
  obtain ⟨he⟩ := lengthConsRecover ((code.relabel j).relabel k) (head.relabel k)
    (tail.relabel k) z count hc' hl' ht
  exact ⟨Derivation.explosion (zeroNeSuc he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
