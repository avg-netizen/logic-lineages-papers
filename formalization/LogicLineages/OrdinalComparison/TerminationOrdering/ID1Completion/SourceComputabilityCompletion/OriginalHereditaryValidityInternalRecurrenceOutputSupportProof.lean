module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity
open OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The unchanged final test has only Boolean outputs on arbitrary states. -/
theorem finishedOutputBoolean (out state : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph1 finished out state))) :
    Nonempty (Derivation body Gamma (eqn out z ⊔ eqn out (numeral 1))) :=
  conjunctionOutputBoolean (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1))
    out (Fin.cons state Fin.elim0) ho

/-- The original validator is Boolean for arbitrary raw inputs, runtime
parameters and binary Program leaves. Only its literal outer composition
is opened; no recurrence, semantic execution or calibrated leaf is used. -/
theorem validatorOutputBoolean (s t m : Program 2) (out raw parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph2 (validator s t m) out raw parameter))) :
    Nonempty (Derivation body Gamma (eqn out z ⊔ eqn out (numeral 1))) := by
  apply programCompositionCases finished (fun _ : Fin 1 => run s t m)
    out (Fin.cons raw (Fin.cons parameter Fin.elim0)) _ ho
  intro beta j ys Delta _ hf _
  change Nonempty (Derivation body Delta
    ((eqn out z).relabel j ⊔ (eqn out (numeral 1)).relabel j))
  simp only [eqnRelabel,zRelabel,numeral,sucRelabel]
  rw [← oneTuple ys] at hf
  exact finishedOutputBoolean (out.relabel j) (ys 0) hf

/-- Contextual nonacceptance forces every actual output to literal zero. -/
theorem validatorOutputReject (s t m : Program 2) (out raw parameter : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph2 (validator s t m) out raw parameter)))
    (hn : Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) raw parameter).not)) :
    Nonempty (Derivation body Gamma (eqn out z)) :=
  booleanOutputReject (validator s t m) out
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) ho
    (validatorOutputBoolean s t m out raw parameter ho) hn

/-- Original Program totality supplies the output internally. Combined
with the proved Boolean law, nonacceptance constructs the actual zero graph. -/
theorem validatorReject (s t m : Program 2) (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) raw parameter).not)) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) z raw parameter)) := by
  apply programCases (validator s t m) (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Delta out hj ho
  simp only [graph2Rename,zRelabel]
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta
    ((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).not) at hn'
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hn'
  simp only [consTermRename,emptyRename] at ho
  exact outputTransport (validator s t m) out z
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (validatorOutputReject s t m out (raw.relabel j) (parameter.relabel j) ho hn') ho

/-- Rejection excludes acceptance at the very same raw input and parameter. -/
theorem validatorZeroNotAccept (s t m : Program 2) (raw parameter : OTerm alpha)
    (hz : Nonempty (Derivation body Gamma (graph2 (validator s t m) z raw parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) raw parameter).not) :=
  zeroOutputNotAccept (validator s t m) (Fin.cons raw (Fin.cons parameter Fin.elim0)) hz

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
