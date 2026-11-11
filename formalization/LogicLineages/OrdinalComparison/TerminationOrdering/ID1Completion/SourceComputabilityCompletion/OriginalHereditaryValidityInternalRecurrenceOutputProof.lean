module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (withHyp)
open OriginalHereditaryValidityInternalRecurrenceProof
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem outputForward (s t m : Program 2) (out raw parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph2 (validator s t m) out raw parameter))) :
    Nonempty (Derivation body Gamma (ValidatorOutputFactors s t m out raw parameter)) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  apply formulaCases A
  · have hv : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique (validator s t m) out (numeral 1)
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) (withHyp ho A) hv
    have he' : Nonempty (Derivation body (A :: Gamma) (equal out (numeral 1))) := by
      simpa only [equalEqn] using he
    obtain ⟨hfields⟩ := andIntro he' (recurrenceForward s t m raw parameter hv)
    exact ⟨orLeft hfields⟩
  · have hn : Nonempty (Derivation body (A.not :: Gamma) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := validatorOutputReject s t m out raw parameter (withHyp ho A.not) hn
    have he' : Nonempty (Derivation body (A.not :: Gamma) (equal out z)) := by
      simpa only [equalEqn] using he
    let F := RecurrenceFactors s t m raw parameter
    have hnf : Nonempty (Derivation body (A.not :: Gamma) F.not) := by
      have hf : Nonempty (Derivation body (F :: A.not :: Gamma) F) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hv⟩ := recurrenceBackward s t m raw parameter hf
      obtain ⟨hn'⟩ := withHyp hn F
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' hv)⟩
    obtain ⟨hfields⟩ := andIntro he' hnf
    exact ⟨orRight hfields⟩

theorem outputBackward (s t m : Program 2) (out raw parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (ValidatorOutputFactors s t m out raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) out raw parameter)) := by
  let F := RecurrenceFactors s t m raw parameter
  let L := equal out (numeral 1) ⊓ F
  let R := equal out z ⊓ F.not
  have leftCase : Nonempty (Derivation body (L :: Gamma) (graph2 (validator s t m) out raw parameter)) := by
    have hh : Nonempty (Derivation body (L :: Gamma) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he : Nonempty (Derivation body (L :: Gamma) (eqn out (numeral 1))) := by
      simpa only [equalEqn] using andLeft hh
    obtain ⟨he⟩ := he
    exact outputTransport (validator s t m) (numeral 1) out
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) ⟨symm he⟩
      (recurrenceBackward s t m raw parameter (andRight hh))
  have rightCase : Nonempty (Derivation body (R :: Gamma) (graph2 (validator s t m) out raw parameter)) := by
    have hh : Nonempty (Derivation body (R :: Gamma) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he : Nonempty (Derivation body (R :: Gamma) (eqn out z)) := by
      simpa only [equalEqn] using andLeft hh
    let A := graph2 (validator s t m) (numeral 1) raw parameter
    have hna : Nonempty (Derivation body (R :: Gamma) A.not) := by
      have hv : Nonempty (Derivation body (A :: R :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hrec⟩ := recurrenceForward s t m raw parameter hv
      obtain ⟨hnf⟩ := withHyp (andRight hh) A
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hnf hrec)⟩
    obtain ⟨he⟩ := he
    exact outputTransport (validator s t m) z out
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) ⟨symm he⟩ (validatorReject s t m raw parameter hna)
  obtain ⟨hf⟩ := hf
  obtain ⟨hl⟩ := leftCase
  obtain ⟨hr⟩ := rightCase
  exact ⟨disjunctionElimination hf (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem actualOriginalHereditaryInternalValidatorOutput :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalValidatorOutput := by
  intro body s t m alpha out raw parameter
  let G := graph2 (validator s t m) out raw parameter
  let F := ValidatorOutputFactors s t m out raw parameter
  obtain ⟨hf⟩ := outputForward s t m out raw parameter
    (show Nonempty (Derivation body [G] G) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := outputBackward s t m out raw parameter
    (show Nonempty (Derivation body [F] F) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputProof
