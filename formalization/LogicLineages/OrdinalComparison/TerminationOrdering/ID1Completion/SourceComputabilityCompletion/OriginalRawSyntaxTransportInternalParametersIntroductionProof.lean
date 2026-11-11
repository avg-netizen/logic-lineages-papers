module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransportInternalParameters OriginalRawSyntaxTransportInternalParametersBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Universal parameter introduction as a continuation, retaining all old
hypotheses under the one actual bound block. -/
theorem atRawIntroFrom (p : Program 3) (rank : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (out d k other otherK : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p out d k (raw.relabel j))) →
      Nonempty (Derivation body Theta
        (graph3 p out other (if rank then otherK else k) (raw.relabel j)))) :
    Nonempty (Derivation body Delta (AtRaw p rank raw)) := by
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let d : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let k : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let other : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let otherK : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := graph3 p out d k (raw.relabel Sum.inl)
  let Theta := A :: Delta.map (fun q => q.relabel Sum.inl)
  obtain ⟨h⟩ := step (alpha ⊕ Fin 5) Sum.inl Theta out d k other otherK
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact atRawIntro p rank raw ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersIntroductionProof
