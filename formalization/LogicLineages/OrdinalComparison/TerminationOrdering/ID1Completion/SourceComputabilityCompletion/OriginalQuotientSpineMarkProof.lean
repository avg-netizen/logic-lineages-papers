module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineMarkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The SAME whole observer values on quotient endpoints are reflected to
raw representatives, used by the literal raw guard, and reinserted at the
quotient endpoints. No equality of separately chosen marks is required. -/
theorem atMarks (data : Data) (window : Program 1) (oldStep : Program 4)
    (hFold : OriginalFullFoldSpine.FullFoldMarkPreservation data window)
    (hStep : OriginalSelectedStepSpine.RawStepHasSpineGuard data oldStep)
    (x y certificate S T K parameter sourceType targetType sm tm sd td : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma (requirements data oldStep x y S T K parameter)))
    (hst : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left sourceType S)))
    (htt : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left targetType T)))
    (hsm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph sm x)))
    (htm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph tm y)))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm))) :
    Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted x y certificate parameter)) := by
  have hstep := andLeft hr
  obtain ⟨hvs,hvt,_⟩ := TypingProof.stepParts data oldStep S T K parameter hstep
  have hfs := TypingProof.sourceFold data x S parameter hvs (andLeft (andRight hr))
  have hft := andRight (andRight hr)
  have hws := BottomDescentStepProof.windowChange window (suc z) x S parameter hw
  have hwt := BottomDescentStepProof.windowChange window (suc z) x T parameter hw
  obtain ⟨hslaw⟩ := hFold body alpha Gamma x S sourceType parameter sm
  obtain ⟨hsinput⟩ := andIntro hws (andIntro (andIntro hvs hst) hfs)
  have hsi := Derivation.implicationElimination hslaw hsinput
  obtain ⟨hsmark⟩ := hsm
  have hrawsm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph sm S)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hsi) hsmark⟩
  obtain ⟨htlaw⟩ := hFold body alpha Gamma y T targetType parameter tm
  obtain ⟨htinput⟩ := andIntro hwt (andIntro (andIntro hvt htt) hft)
  have hti := Derivation.implicationElimination htlaw htinput
  obtain ⟨htmark⟩ := htm
  have hrawtm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph tm T)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hti) htmark⟩
  obtain ⟨hguardLaw⟩ := hStep body alpha Gamma S T K parameter
  obtain ⟨hstep'⟩ := hstep
  have hrawGuard : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted S T K parameter)) :=
    ⟨Derivation.implicationElimination hguardLaw hstep'⟩
  let rawInputs : Fin 4 → OTerm alpha :=
    Fin.cons S (Fin.cons T (Fin.cons K (Fin.cons parameter Fin.elim0)))
  let quotientInputs : Fin 4 → OTerm alpha :=
    Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hc := PositiveSpineRulesProof.spineRecover BottomSpineMeasure.measure sm tm sd td
    rawInputs hrawsm hrawtm hsd htd hrawGuard
  exact PositiveSpineRulesProof.spineValue BottomSpineMeasure.measure sm tm sd td
    quotientInputs ⟨hsmark⟩ ⟨htmark⟩ hsd htd hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineMarkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineMarkProof
