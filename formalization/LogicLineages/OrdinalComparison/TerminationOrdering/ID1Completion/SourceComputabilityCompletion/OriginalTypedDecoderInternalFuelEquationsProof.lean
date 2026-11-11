module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelEquationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof InternalAdditionLawsProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)

theorem actualOriginalTypedInternalWorkFuelEquations :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalWorkFuelEquations := by
  refine ⟨?_, ?_, ?_⟩
  · intro body alpha request mode gamma typ raw out
    let A := StepRequest request mode gamma typ raw
    let P := graph1 requestFuel out request
    let Q := equal out (suc raw)
    have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := requestValue request mode gamma typ raw ha
    have hf : Nonempty (Derivation body [P,A] Q) := by
      change Nonempty (Derivation body [P,A] (equal out (suc raw)))
      rw [equalEqn]
      exact valueUnique requestFuel out (suc raw) (Fin.cons request Fin.elim0)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv P)
    have hb : Nonempty (Derivation body [Q,A] P) := by
      have he : Derivation body [Q,A] (eqn out (suc raw)) := by
        rw [← equalEqn]; exact Derivation.hypothesis List.mem_cons_self
      exact outputTransport requestFuel (suc raw) out (Fin.cons request Fin.elim0)
        ⟨symm he⟩ (withHyp hv Q)
    obtain ⟨hf⟩ := hf
    obtain ⟨hb⟩ := hb
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
  · intro body alpha out
    exact graphIffValue out z z nilValue
  · intro body alpha code request mode gamma typ raw rest tail out
    let A := StepCons code request rest ⊓
      (StepRequest request mode gamma typ raw ⊓ WorkFuelGraph tail rest)
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := consValue code request rest (suc raw) tail (andLeft h)
      (requestValue request mode gamma typ raw (andLeft (andRight h)))
      (andRight (andRight h))
    obtain ⟨d⟩ := graphIffValue out (add (suc raw) tail) code hv
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelEquationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelEquationsProof
