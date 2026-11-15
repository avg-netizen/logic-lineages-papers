module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem guardCases (n : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (h0 : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (OriginalCodeValidityGuard.check n) z (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (h1 : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply programCases (OriginalCodeValidityGuard.check n) (Fin.cons raw Fin.elim0) psi
  intro beta j Theta control hj hg
  simp only [consTermRename,emptyRename] at hg
  have hr := GuardRangeProof.guardRange n body beta Theta (raw.relabel j) control hg
  have a : Nonempty (Derivation body Theta ((eqn control z).imp (psi.relabel j))) := by
    have hc := outputTransport (OriginalCodeValidityGuard.check n) control z (Fin.cons (raw.relabel j) Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hg (eqn control z))
    obtain ⟨hp⟩ := h0 beta j (eqn control z :: Theta) (fun p hp => List.mem_cons_of_mem _ (hj p hp)) hc
    exact ⟨Derivation.implicationIntroduction hp⟩
  have b : Nonempty (Derivation body Theta ((eqn control (suc z)).imp (psi.relabel j))) := by
    have hc := outputTransport (OriginalCodeValidityGuard.check n) control (suc z) (Fin.cons (raw.relabel j) Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hg (eqn control (suc z)))
    obtain ⟨hp⟩ := h1 beta j (eqn control (suc z) :: Theta) (fun p hp => List.mem_cons_of_mem _ (hj p hp)) hc
    exact ⟨Derivation.implicationIntroduction hp⟩
  obtain ⟨hr⟩ := hr
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hr a b⟩

theorem positiveRecover (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param))) :
    Nonempty (Derivation body Delta (graph2 (OriginalBoundsRecombination.recombine n) out raw answers)) := by
  have hv := InternalAcceptanceBranchProof.successorBranchElim (accepted n) (InternalLessThan.constantOne 3)
    (.composition (OriginalBoundsRecombination.recombine n) ![.projection 0,.projection 1]) out z
    ![raw,answers,param] (SupportProof.acceptedValue n raw answers param (suc z) hg) ho
  exact InternalApplicationCertificateConstructorsSupportProof.binaryRecover
    (OriginalBoundsRecombination.recombine n) (.projection 0) (.projection 1)
    out raw answers ![raw,answers,param] hv (projectionValue 0 ![raw,answers,param])
    (projectionValue 1 ![raw,answers,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
