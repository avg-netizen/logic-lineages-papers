module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceNormalizationProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalGraphCompositionFunctionalityProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalQuotientComparisonProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Booleanity is proved from the original internal normalizer graph.
The source Program may return any natural number. -/
theorem normalizeOutputBoolean {n : Nat} (p : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (programGraph (normalize p) out xs))) :
    Nonempty (Derivation body Gamma (eqn out z ⊔ eqn out (suc z))) := by
  let P := programGraph p (suc z) xs
  obtain ⟨ho⟩ := ho
  have hy : Nonempty (Derivation body (P :: Gamma) (eqn out z ⊔ eqn out (suc z))) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique (normalize p) out (suc z) xs
      ⟨addHyp ho P⟩ (normalizeAccept p xs hp)
    exact ⟨orRight he⟩
  have hn : Nonempty (Derivation body (P.not :: Gamma) (eqn out z ⊔ eqn out (suc z))) := by
    have hp : Nonempty (Derivation body (P.not :: Gamma) P.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique (normalize p) out z xs
      ⟨addHyp ho P.not⟩ (normalizeReject p xs hp)
    exact ⟨orLeft he⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Every output of the original conjunction is literally zero or one,
without any Boolean hypothesis on either input Program. -/
theorem conjunctionOutputBoolean {n : Nat} (p q : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (programGraph (conjunction p q) out xs))) :
    Nonempty (Derivation body Gamma (eqn out z ⊔ eqn out (suc z))) := by
  let P := programGraph p (suc z) xs
  obtain ⟨ho⟩ := ho
  have hy : Nonempty (Derivation body (P :: Gamma) (eqn out z ⊔ eqn out (suc z))) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact normalizeOutputBoolean q out xs
      (successorBranchElim (normalize p) (constantZero n) (normalize q)
        out z xs (normalizeAccept p xs hp) ⟨addHyp ho P⟩)
  have hn : Nonempty (Derivation body (P.not :: Gamma) (eqn out z ⊔ eqn out (suc z))) := by
    have hp : Nonempty (Derivation body (P.not :: Gamma) P.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := zeroBranchElim (normalize p) (constantZero n) (normalize q)
      out xs (normalizeReject p xs hp) ⟨addHyp ho P.not⟩
    obtain ⟨he⟩ := valueUnique (constantZero n) out z xs hz (constantZeroValue xs)
    exact ⟨orLeft he⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Functionality alone excludes simultaneous literal rejection and acceptance. -/
theorem zeroOutputNotAccept {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (hz : Nonempty (Derivation body Gamma (programGraph p z xs))) :
    Nonempty (Derivation body Gamma (programGraph p (suc z) xs).not) := by
  let P := programGraph p (suc z) xs
  obtain ⟨hz⟩ := hz
  obtain ⟨he⟩ := valueUnique p (suc z) z xs
    (show Nonempty (Derivation body (P :: Gamma) P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp hz P⟩
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

/-- At any given Boolean graph output, failure of exact-one acceptance
forces that output to be zero. This is entirely contextual. -/
theorem booleanOutputReject {n : Nat} (p : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (programGraph p out xs)))
    (hb : Nonempty (Derivation body Gamma (eqn out z ⊔ eqn out (suc z))))
    (hn : Nonempty (Derivation body Gamma (programGraph p (suc z) xs).not)) :
    Nonempty (Derivation body Gamma (eqn out z)) := by
  let Z := eqn out z
  let O := eqn out (suc z)
  obtain ⟨ho⟩ := ho
  obtain ⟨hn⟩ := hn
  have hy : Derivation body (Z :: Gamma) Z := Derivation.hypothesis List.mem_cons_self
  have hf : Nonempty (Derivation body (O :: Gamma) Z) := by
    obtain ⟨ha⟩ := outputTransport p out (suc z) xs
      (show Nonempty (Derivation body (O :: Gamma) O) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp ho O⟩
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn O) ha)⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hf⟩ := hf
  exact ⟨disjunctionElimination hb
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hf)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
