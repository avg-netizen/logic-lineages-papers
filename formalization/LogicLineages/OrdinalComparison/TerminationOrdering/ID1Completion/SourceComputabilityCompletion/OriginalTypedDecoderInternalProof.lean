module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof (symm)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalStateSyntaxProof OriginalTypedDecoderInternalStateProof
open OriginalTypedDecoderInternalModeProof OriginalTypedDecoderInternalBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem identityForward (out input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 (.projection 0) out input))) :
    Nonempty (Derivation body Delta (equal out input)) := by
  simpa only [equalEqn] using valueUnique (.projection (0 : Fin 1)) out input
    (Fin.cons input Fin.elim0) h (projectionValue 0 (Fin.cons input Fin.elim0))

 theorem identityBackward (out input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (equal out input))) :
    Nonempty (Derivation body Delta (graph1 (.projection 0) out input)) := by
  have he : Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn out input)) := by
    simpa only [equalEqn] using h
  obtain ⟨he⟩ := he
  exact outputTransport (.projection (0 : Fin 1)) input out (Fin.cons input Fin.elim0)
    ⟨symm he⟩ (projectionValue 0 (Fin.cons input Fin.elim0))

/-- Open actual status and work internally, retaining both failure and the
live-empty fixed point before connecting a genuine nonempty request. -/
 theorem fullForward (H : Program 1) (out input : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 (transition H) out input))) :
    Nonempty (Derivation body Delta (stepSpec H out input)) := by
  apply queryCases (![status,work] : Fin 2 → Program 1) (Fin.cons input Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stateRename]
  have ho' := renameInto ho j Theta hj
  rw [graph1Rename] at ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
  let live := InternalAcceptance.branch work (.projection 0) (modeProgram H)
  have hpair := reconstructPair (input.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
  apply stateIntro H _ _ ys
  apply andIntro hpair
  apply formulaCases (equal (ys 0) (numeral 1)) _
  · have hs : Nonempty (Derivation body (equal (ys 0) (numeral 1) :: Theta)
        (equal (ys 0) (numeral 1))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlive := sameYesElim status (constant 1 1) live (constant 1 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp (hq 0) _) (constantValue 1 xx) hs (withHyp ho' _)
    apply formulaCases (equal (ys 1) (numeral 0)) _
    · have hwzero : Nonempty (Derivation body
          (equal (ys 1) (numeral 0) :: equal (ys 0) (numeral 1) :: Theta)
          (equal (ys 1) (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hidentity := zeroAtElim work (.projection 0) (modeProgram H) (out.relabel j) (ys 1) xx
        (withHyp (withHyp (hq 1) _) _) hwzero (withHyp hlive _)
      obtain ⟨he⟩ := andIntro hwzero (identityForward (out.relabel j) (input.relabel j) hidentity)
      obtain ⟨hs⟩ := withHyp hs (equal (ys 1) (numeral 0))
      exact ⟨orRight (Derivation.conjunctionIntroduction hs (orLeft he))⟩
    · have hwnonzero : Nonempty (Derivation body
          ((equal (ys 1) (numeral 0)).not :: equal (ys 0) (numeral 1) :: Theta)
          (equal (ys 1) (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hmode := nonzeroAtElim work (.projection 0) (modeProgram H) (out.relabel j) (ys 1) xx
        (withHyp (withHyp (hq 1) _) _) hwnonzero (withHyp hlive _)
      have hnonempty := nonemptyForward H (input.relabel j) (out.relabel j) (ys 1)
        (withHyp (withHyp (hq 1) _) _) hwnonzero hmode
      obtain ⟨he⟩ := andIntro hwnonzero hnonempty
      obtain ⟨hs⟩ := withHyp hs (equal (ys 1) (numeral 0)).not
      exact ⟨orRight (Derivation.conjunctionIntroduction hs (orRight he))⟩
  · have hs : Nonempty (Derivation body ((equal (ys 0) (numeral 1)).not :: Theta)
        (equal (ys 0) (numeral 1)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hzero := sameNoElim status (constant 1 1) live (constant 1 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp (hq 0) _) (constantValue 1 xx) hs (withHyp ho' _)
    obtain ⟨he⟩ := andIntro hs (constantForward 0 (out.relabel j) xx hzero)
    exact ⟨orLeft he⟩

/-- Rebuild the identical finite transition AST from the independent arithmetic
specification. No native calibration or successful-run assumption is used. -/
 theorem fullBackward (H : Program 1) (out input : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (stepSpec H out input))) :
    Nonempty (Derivation body Delta (graph1 (transition H) out input)) := by
  apply stateCases H out input _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  let xx : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
  let liveProgram := InternalAcceptance.branch work (.projection 0) (modeProgram H)
  have hs := pairLeft (input.relabel j) (ys 0) (ys 1) (andLeft hq)
  have hw := pairRight (input.relabel j) (ys 0) (ys 1) (andLeft hq)
  let rejected : Formula beta := (equal (ys 0) (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0)
  let empty : Formula beta := equal (ys 1) (numeral 0) ⊓ equal (out.relabel j) (input.relabel j)
  let pending : Formula beta := (equal (ys 1) (numeral 0)).not ⊓ StepNonemptyWork H (out.relabel j) (ys 1)
  let active : Formula beta := equal (ys 0) (numeral 1) ⊓ (empty ⊔ pending)
  apply orCases (andRight hq)
  · have hbad : Nonempty (Derivation body (rejected :: Theta) rejected) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameNoIntro status (constant 1 1) liveProgram (constant 1 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp hs _) (constantValue 1 xx) (andLeft hbad)
      (constantBackward 0 (out.relabel j) xx (andRight hbad))
  · have hgood : Nonempty (Derivation body (active :: Theta) active) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases (andRight hgood)
    · have hempty : Nonempty (Derivation body (empty :: active :: Theta) empty) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameYesIntro status (constant 1 1) liveProgram (constant 1 0)
        (out.relabel j) (ys 0) (numeral 1) xx (withHyp (withHyp hs _) _) (constantValue 1 xx)
        (withHyp (andLeft hgood) _)
      exact zeroAtIntro work (.projection 0) (modeProgram H) (out.relabel j) (ys 1) xx
        (withHyp (withHyp hw _) _) (andLeft hempty)
        (identityBackward (out.relabel j) (input.relabel j) (andRight hempty))
    · have hpending : Nonempty (Derivation body (pending :: active :: Theta) pending) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameYesIntro status (constant 1 1) liveProgram (constant 1 0)
        (out.relabel j) (ys 0) (numeral 1) xx (withHyp (withHyp hs _) _) (constantValue 1 xx)
        (withHyp (andLeft hgood) _)
      apply nonzeroAtIntro work (.projection 0) (modeProgram H) (out.relabel j) (ys 1) xx
        (withHyp (withHyp hw _) _) (andLeft hpending)
      exact nonemptyBackward H (input.relabel j) (out.relabel j) (ys 1)
        (withHyp (withHyp hw _) _) (andRight hpending)

 theorem actualOriginalTypedInternalStep : OriginalTypedDecoderTargets.ActualOriginalTypedInternalStep := by
  intro H body alpha out input
  obtain ⟨hf⟩ := fullForward (body := body) (Delta := [graph1 (transition H) out input]) H out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := fullBackward (body := body) (Delta := [stepSpec H out input]) H out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
