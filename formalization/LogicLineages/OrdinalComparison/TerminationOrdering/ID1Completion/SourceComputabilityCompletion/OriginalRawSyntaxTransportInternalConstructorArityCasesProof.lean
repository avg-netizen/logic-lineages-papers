module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorArityProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Context-preserving use of the original logical disjunction rule. -/
theorem orCases {p q psi : Formula alpha}
    (h : Nonempty (Derivation body Delta (p ⊔ q)))
    (hl : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta p) → Nonempty (Derivation body Theta psi))
    (hr : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta q) → Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl (p :: Delta) (fun a ha => List.mem_cons_of_mem _ ha)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := hr (q :: Delta) (fun a ha => List.mem_cons_of_mem _ ha)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction hr)⟩

theorem arityRange (raw out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) out raw))) :
    Nonempty (Derivation body Delta
      (equal out (numeral 0) ⊔ (equal out (numeral 1) ⊔ equal out (numeral 2)))) := by
  apply orCases (arityView raw out ha)
  · intro Theta inc he
    obtain ⟨he⟩ := he
    exact ⟨orLeft he⟩
  · intro Theta inc hu
    apply orCases hu
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨orRight (orLeft (Derivation.conjunctionLeft he))⟩
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨orRight (orRight (Derivation.conjunctionLeft he))⟩

theorem arityOneTags (raw : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw ⊔ graph1 rawTag (numeral 4) raw)) := by
  apply orCases (arityView raw (numeral 1) ha)
  · intro Theta inc he
    obtain ⟨he⟩ := he
    exact ⟨Derivation.explosion (numeralNeApply 1 0 (by decide) (by simpa only [equalEqn] using he))⟩
  · intro Theta inc hu
    apply orCases hu
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨Derivation.conjunctionRight he⟩
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨Derivation.explosion (numeralNeApply 1 2 (by decide)
        (by simpa only [equalEqn] using Derivation.conjunctionLeft he))⟩

theorem arityTwoTags (raw : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw))) :
    Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw ⊔
      (graph1 rawTag (numeral 5) raw ⊔ graph1 rawTag (numeral 7) raw))) := by
  apply orCases (arityView raw (numeral 2) ha)
  · intro Theta inc he
    obtain ⟨he⟩ := he
    exact ⟨Derivation.explosion (numeralNeApply 2 0 (by decide) (by simpa only [equalEqn] using he))⟩
  · intro Theta inc hu
    apply orCases hu
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨Derivation.explosion (numeralNeApply 2 1 (by decide)
        (by simpa only [equalEqn] using Derivation.conjunctionLeft he))⟩
    · intro Xi inc' he
      obtain ⟨he⟩ := he
      exact ⟨Derivation.conjunctionRight he⟩

theorem arityGraphCases (raw out : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) out raw)))
    (k0 : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 0) raw)) →
      Nonempty (Derivation body Theta psi))
    (k1 : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 1) raw)) →
      Nonempty (Derivation body Theta psi))
    (k2 : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 2) raw)) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) := by
  apply orCases (arityRange raw out ha)
  · intro Theta inc he
    exact k0 Theta inc (outputTransport (arityOf (.projection 0)) out (numeral 0)
      (Fin.cons raw Fin.elim0) (by simpa only [equalEqn] using he) (weakenProof ha inc))
  · intro Theta inc hs
    apply orCases hs
    · intro Xi inc' he
      have hm : ∀ a ∈ Delta, a ∈ Xi := fun a ha => inc' a (inc a ha)
      exact k1 Xi hm (outputTransport (arityOf (.projection 0)) out (numeral 1)
        (Fin.cons raw Fin.elim0) (by simpa only [equalEqn] using he) (weakenProof ha hm))
    · intro Xi inc' he
      have hm : ∀ a ∈ Delta, a ∈ Xi := fun a ha => inc' a (inc a ha)
      exact k2 Xi hm (outputTransport (arityOf (.projection 0)) out (numeral 2)
        (Fin.cons raw Fin.elim0) (by simpa only [equalEqn] using he) (weakenProof ha hm))

/-- Original totality supplies the arity witness, which is eliminated inside
arithmetic; callers receive only the three actual possible graph outputs. -/
theorem arityCases (raw : OTerm alpha) (psi : Formula alpha)
    (k0 : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ a ∈ Delta, a.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 0) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (k1 : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ a ∈ Delta, a.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 1) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (k2 : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ a ∈ Delta, a.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (arityOf (.projection 0)) (numeral 2) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases (arityOf (.projection 0)) (Fin.cons raw Fin.elim0) psi
  intro beta j Theta out hj ha
  simp only [consTermRename,emptyRename] at ha
  apply arityGraphCases (raw.relabel j) out (psi.relabel j) ha
  · intro Xi inc h
    exact k0 beta j Xi (fun a ha => inc (a.relabel j) (hj a ha)) h
  · intro Xi inc h
    exact k1 beta j Xi (fun a ha => inc (a.relabel j) (hj a ha)) h
  · intro Xi inc h
    exact k2 beta j Xi (fun a ha => inc (a.relabel j) (hj a ha)) h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
