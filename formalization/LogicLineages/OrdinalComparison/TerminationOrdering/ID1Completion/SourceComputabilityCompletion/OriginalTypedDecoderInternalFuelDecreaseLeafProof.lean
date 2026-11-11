module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreasePushProof
open OriginalTypedDecoderInternalVariableSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem weakenProof {phi : Formula alpha} {Theta : List (Formula alpha)}
    (h : Nonempty (Derivation body Delta phi)) (inc : ∀ p ∈ Delta, p ∈ Theta) :
    Nonempty (Derivation body Theta phi) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.weakening inc h⟩

 theorem choiceCases {p q psi : Formula alpha}
    (h : Nonempty (Derivation body Delta (p ⊔ q)))
    (left : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta p) → Nonempty (Derivation body Theta psi))
    (right : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta q) → Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases h
  · exact left (p :: Delta) (fun a ha => List.mem_cons_of_mem _ ha)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact right (q :: Delta) (fun a ha => List.mem_cons_of_mem _ ha)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

 theorem guardedPopDecrease (out rest raw tail previous : OTerm alpha)
    (yes no : Formula alpha)
    (h : Nonempty (Derivation body Delta
      ((yes ⊓ StepLive out rest) ⊔ (no ⊓ equal out (numeral 0)))))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply choiceCases h
  · intro Theta inc hy
    exact poppedDecrease out rest raw tail previous (andRight hy)
      (weakenProof ht inc) (weakenProof he inc)
  · intro Theta inc hn
    exact failedIntro out previous (andRight hn)

 theorem variableDecrease (out gamma typ index rest raw tail previous : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepVariable out gamma typ index rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepVariableCases out gamma typ index rest _ h
  intro beta j Theta value hj fields
  rw [decreasedRename]
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  exact guardedPopDecrease (out.relabel j) (rest.relabel j) (raw.relabel j)
    (tail.relabel j) (previous.relabel j) _ _ (andRight fields) ht' he'

 theorem bottomDecrease (out typ payload rest raw tail previous : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepBottom out typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) :=
  guardedPopDecrease out rest raw tail previous _ _ h ht he

 theorem nilDecrease (out typ payload rest raw tail previous : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepArgumentsNil out typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) :=
  guardedPopDecrease out rest raw tail previous _ _ h ht he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseLeafProof
