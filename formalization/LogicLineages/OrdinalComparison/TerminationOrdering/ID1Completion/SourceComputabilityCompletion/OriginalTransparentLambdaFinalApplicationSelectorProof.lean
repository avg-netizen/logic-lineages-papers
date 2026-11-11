module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalApplicationValidityClosure
open OriginalHereditaryValidity OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
open OriginalHereditaryValidityInternalRecurrenceRootFrameProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rawTypeAndTag (arrow d e fp ap fn arg raw : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg raw))) :
    Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.left e raw ⊓ graph1 OriginalLambdaConstructor.tag (numeral 2) raw)) := by
  have hp := andRight (andRight (andRight hc))
  have ht := andLeft (OriginalApplicationComponentCoherenceFieldsProof.packedFields d e fp ap raw hp)
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have htype := unaryRecover InternalUnpair.left (.projection 0) e raw xs ht (projectionValue 0 xs)
  exact andIntro htype (andLeft (OriginalConstructorShapeApplicationProof.packedFields d e fp ap raw hp))

theorem childrenEquationAt (s t m : Program 2)
    (state arrow d e fp ap fn arg raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg raw)))
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter))) :
    Nonempty (Derivation body Gamma
      ((RootApplicationChildren s t m raw parameter).iff
        (graph2 (validator s t m) (numeral 1) fn parameter ⊓
          graph2 (validator s t m) (numeral 1) arg parameter))) := by
  have hsel := OriginalTransparentLambdaFinalApplicationFieldsProof.currentChildren
    state arrow d e fp ap fn arg raw parameter hc hi
  let P := RootApplicationChildren s t m raw parameter
  let Q := graph2 (validator s t m) (numeral 1) fn parameter ⊓
    graph2 (validator s t m) (numeral 1) arg parameter
  have lift {R : Formula alpha} (h : Nonempty (Derivation body Gamma R)) (A : Formula alpha) :
      Nonempty (Derivation body (A :: Gamma) R) := by
    obtain ⟨h⟩ := h
    exact ⟨InternalBetaTotalityProof.addHyp h A⟩
  have hf : Nonempty (Derivation body (P :: Gamma) Q) :=
    rootApplicationAt s t m raw parameter state fn arg (lift hi P)
      (lift (andLeft hsel) P) (lift (andRight hsel) P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (Q :: Gamma) P) := by
    have hq : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact rootApplicationIntro s t m raw parameter state fn arg
      (andIntro (lift hi Q) (andIntro (lift (andLeft hsel) Q)
        (andIntro (andIntro (lift (andRight hsel) Q) (andLeft hq)) (andRight hq))))
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The initial state and both actual child selectors are supplied internally;
no child validity, semantic decoding, or frame premise is assumed. -/
theorem childrenEquation (s t m : Program 2)
    (arrow d e fp ap fn arg raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg raw))) :
    Nonempty (Derivation body Gamma
      ((RootApplicationChildren s t m raw parameter).iff
        (graph2 (validator s t m) (numeral 1) fn parameter ⊓
          graph2 (validator s t m) (numeral 1) arg parameter))) := by
  apply rootFrameCases raw parameter _
  intro beta j Delta state work frame payload hj hi _ _
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  change Nonempty (Derivation body Delta
    (((RootApplicationChildren s t m raw parameter).relabel j).iff
      (((graph2 (validator s t m) (numeral 1) fn parameter).relabel j) ⊓
        ((graph2 (validator s t m) (numeral 1) arg parameter).relabel j))))
  rw [rootApplicationRename,graph2Rename,graph2Rename,oneRename]
  exact childrenEquationAt s t m state (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (raw.relabel j)
    (parameter.relabel j) hc' hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationSelectorProof
