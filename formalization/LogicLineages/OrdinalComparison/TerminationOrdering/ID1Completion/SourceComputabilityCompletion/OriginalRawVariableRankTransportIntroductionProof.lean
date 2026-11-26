module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportBindingProof

theorem atRawIntroFrom (p : Program 3) (erasing : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (d k transformed before after : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p transformed d k (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 variableRankRaw before (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 variableRankRaw after transformed)) →
      Nonempty (Derivation body Theta (RankRelation erasing after before))) :
    Nonempty (Derivation body Delta (AtRaw p erasing raw)) := by
  let d : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let k : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let transformed : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let before : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let after : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := graph3 p transformed d k (raw.relabel Sum.inl) ⊓
    (graph1 variableRankRaw before (raw.relabel Sum.inl) ⊓ graph1 variableRankRaw after transformed)
  let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
  have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := step (alpha ⊕ Fin 5) Sum.inl Theta d k transformed before after
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact atRawIntro p erasing raw ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportIntroductionProof
