module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationTagCases (input parameter : OTerm α) (psi : Formula α)
    (htag : Nonempty (Derivation body Gamma (OriginalTransparentLambdaValidityInternal.TagIs 2 input)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (payload arrow d e fp ap fn arg : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg
          (input.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload (input.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)) →
      Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)) →
      Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let guard := InternalLessThan.constantOne 2
  have ht := sameAccept (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)
    (numeral 2) (Fin.cons input Fin.elim0) htag (twoValue (Fin.cons input Fin.elim0))
  have hl := InternalParameterizedApplicationResultStackWiringProof.liftValue _
    (numeral 1) input parameter ht
  have hg := conjunctionAccept _ guard (Fin.cons input (Fin.cons parameter Fin.elim0)) hl
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons input (Fin.cons parameter Fin.elim0)))
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases guard input parameter psi hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hp hf ha hfp hap _
  exact k β j Delta payload arrow d e fp ap fn arg hj hc hp hf ha hfp hap

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOpeningProof
