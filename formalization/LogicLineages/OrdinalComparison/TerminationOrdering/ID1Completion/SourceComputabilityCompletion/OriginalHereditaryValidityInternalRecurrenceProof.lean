module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (withHyp)
open OriginalHereditaryValidityInternalRecurrenceApplicationProof
open OriginalHereditaryValidityInternalRecurrenceLambdaProof
open OriginalHereditaryValidityInternalRecurrencePopProof
open OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem recurrenceForward (s t m : Program 2) (raw parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma (graph2 (validator s t m) (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (RecurrenceFactors s t m raw parameter)) := by
  have hn := acceptanceFactors s t m raw parameter hv
  apply programCases OriginalLambdaConstructor.tag (Fin.cons raw Fin.elim0) _
  intro beta j Delta tag hj ht
  rw [recurrenceRename]
  simp only [consTermRename,emptyRename] at ht
  have hn' := renameInto hn j Delta hj
  rw [factorsRename] at hn'
  have hv' := renameInto hv j Delta hj
  simp only [graph2Rename,oneRename] at hv'
  have happ : Nonempty (Derivation body Delta
      ((equal tag (numeral 2)).imp (RootApplicationChildren s t m (raw.relabel j) (parameter.relabel j)))) := by
    let A := equal tag (numeral 2)
    have he : Nonempty (Derivation body (A :: Delta) (eqn tag (numeral 2))) := by
      simpa only [A,equalEqn] using
        (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have htag := outputTransport OriginalLambdaConstructor.tag tag (numeral 2)
      (Fin.cons (raw.relabel j) Fin.elim0) he (withHyp ht A)
    obtain ⟨hrec⟩ := applicationRecurrence s t m (raw.relabel j) (parameter.relabel j) (withHyp hn' A) htag
    obtain ⟨hval⟩ := withHyp hv' A
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionLeft hrec) hval)⟩
  have hlam : Nonempty (Derivation body Delta
      ((equal tag (numeral 1)).imp (RootLambdaChild s t m (raw.relabel j) (parameter.relabel j)))) := by
    let A := equal tag (numeral 1)
    have he : Nonempty (Derivation body (A :: Delta) (eqn tag (numeral 1))) := by
      simpa only [A,equalEqn] using
        (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have htag := outputTransport OriginalLambdaConstructor.tag tag (numeral 1)
      (Fin.cons (raw.relabel j) Fin.elim0) he (withHyp ht A)
    obtain ⟨hrec⟩ := lambdaRecurrence s t m (raw.relabel j) (parameter.relabel j) (withHyp hn' A) htag
    obtain ⟨hval⟩ := withHyp hv' A
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionLeft hrec) hval)⟩
  exact recurrenceIntro s t m (raw.relabel j) (parameter.relabel j) tag hn'
    (andIntro ht (andIntro happ hlam))

theorem recurrenceBackward (s t m : Program 2) (raw parameter : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (RecurrenceFactors s t m raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) (numeral 1) raw parameter)) := by
  apply recurrenceCases s t m raw parameter _ hr
  intro beta j Delta tag hj hn fields
  simp only [graph2Rename,oneRename]
  let A := equal tag (numeral 2)
  apply formulaCases A
  · have he : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
    have htag := outputTransport OriginalLambdaConstructor.tag tag (numeral 2)
      (Fin.cons (raw.relabel j) Fin.elim0) (by simpa only [A,equalEqn] using Nonempty.intro he)
      (withHyp (andLeft fields) A)
    obtain ⟨hrec⟩ := applicationRecurrence s t m (raw.relabel j) (parameter.relabel j) (withHyp hn A) htag
    obtain ⟨happ⟩ := withHyp (andLeft (andRight fields)) A
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrec)
      (Derivation.implicationElimination happ he)⟩
  · let B := equal tag (numeral 1)
    apply formulaCases B
    · have he : Derivation body (B :: A.not :: Delta) B := Derivation.hypothesis List.mem_cons_self
      have htag := outputTransport OriginalLambdaConstructor.tag tag (numeral 1)
        (Fin.cons (raw.relabel j) Fin.elim0) (by simpa only [B,equalEqn] using Nonempty.intro he)
        (withHyp (withHyp (andLeft fields) A.not) B)
      obtain ⟨hrec⟩ := lambdaRecurrence s t m (raw.relabel j) (parameter.relabel j)
        (withHyp (withHyp hn A.not) B) htag
      obtain ⟨hlam⟩ := withHyp (withHyp (andRight (andRight fields)) A.not) B
      exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrec)
        (Derivation.implicationElimination hlam he)⟩
    · exact popRecurrence s t m (raw.relabel j) (parameter.relabel j) tag
        (withHyp (withHyp hn A.not) B.not) (withHyp (withHyp (andLeft fields) A.not) B.not)
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem recurrenceIff (s t m : Program 2) (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (RecurrenceFactors s t m raw parameter))) := by
  obtain ⟨hf⟩ := recurrenceForward s t m raw parameter
    (show Nonempty (Derivation body ((graph2 (validator s t m) (numeral 1) raw parameter) :: Gamma)
      (graph2 (validator s t m) (numeral 1) raw parameter)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := recurrenceBackward s t m raw parameter
    (show Nonempty (Derivation body ((RecurrenceFactors s t m raw parameter) :: Gamma)
      (RecurrenceFactors s t m raw parameter)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalHereditaryInternalValidatorRecurrence :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalValidatorRecurrence := by
  intro body s t m alpha raw parameter
  exact recurrenceIff s t m raw parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceProof
