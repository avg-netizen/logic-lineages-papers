module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.GuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114.HeadWindowBooleanRange
open ProgramRangeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalHeadDecoderValidity
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem chooseRange (tag : Nat) (yes no : Program 1) (hy : Ranged yes) (hn : Ranged no) :
    Ranged (Continuation20261114.OriginalHeadEncodingBridge.choose tag yes no) := branchRange _ _ _ hn hy

theorem ranged (n : Nat) : Ranged (check n) :=
  chooseRange _ _ _ (Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof.sameRange _ _)
    (chooseRange _ _ _ (Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof.sameRange _ _)
      (chooseRange _ _ _ (constantRange 1 1)
        (chooseRange _ _ _ (constantRange 1 1)
          (chooseRange _ _ _ (constantRange 1 1)
            (chooseRange _ _ _ (compositionRange _ _ OriginalEnumerationFields.Boolean.LayerPointProof.ltRange)
              (constantRange 1 0))))))

theorem cases (n : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (hz : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (check n) z (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (hs : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (check n) (suc z) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply programCases (check n) ![raw] _
  intro beta j Theta value hj hc
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i; rfl
  rw [hx] at hc
  have hb := ranged n body beta Theta value ![raw.relabel j] hc
  apply OriginalTypedDecoderInternalBranchProof.orCases hb
  · have he : Nonempty (Derivation body (eqn value z :: Theta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact hz beta j _ (fun p hp => List.mem_cons_of_mem _ (hj p hp))
      (outputTransport (check n) value z ![raw.relabel j] he (withHyp hc _))
  · have he : Nonempty (Derivation body (eqn value (suc z) :: Theta) (eqn value (suc z))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact hs beta j _ (fun p hp => List.mem_cons_of_mem _ (hj p hp))
      (outputTransport (check n) value (suc z) ![raw.relabel j] he (withHyp hc _))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.GuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.GuardProof
