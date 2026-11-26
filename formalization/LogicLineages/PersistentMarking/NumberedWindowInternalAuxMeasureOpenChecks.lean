module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureOpenTargets
open NumberedWindowInternalAuxMeasureOpenEvaluationProof (deriveValue measureRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem equalAfterCombination (base : Program 1) (P : Program 2)
    (dom cod fn fn' arg mf ma common x y : OTerm α)
    (functionA : Nonempty (Derivation body Γ (measureGraph base P mf fn)))
    (functionB : Nonempty (Derivation body Γ (measureGraph base P mf fn')))
    (argument : Nonempty (Derivation body Γ (measureGraph base P ma arg)))
    (parentA : Nonempty (Derivation body Γ (measureGraph base P x (auxiliaryTerm dom cod fn arg))))
    (parentB : Nonempty (Derivation body Γ (measureGraph base P y (auxiliaryTerm dom cod fn' arg))))
    (emit : Nonempty (Derivation body Γ (programGraph P common ![mf,ma]))) :
    Nonempty (Derivation body Γ (eqn x y)) := by
  let M := selectedMeasure (measureUpdate base P)
  let a := auxiliaryTerm dom cod fn arg
  let b := auxiliaryTerm dom cod fn' arg
  have left := deriveValue base P dom cod fn arg mf ma common functionA argument emit
  have right := deriveValue base P dom cod fn' arg mf ma common functionB argument emit
  obtain ⟨sameLeft⟩ := valueUnique M x common ![a] parentA left
  obtain ⟨sameRight⟩ := valueUnique M common y ![b] right parentB
  exact ⟨trans sameLeft sameRight⟩

private theorem equalAfterArgument (base : Program 1) (P : Program 2)
    (dom cod fn fn' arg mf ma x y : OTerm α)
    (functionA : Nonempty (Derivation body Γ (measureGraph base P mf fn)))
    (functionB : Nonempty (Derivation body Γ (measureGraph base P mf fn')))
    (argument : Nonempty (Derivation body Γ (measureGraph base P ma arg)))
    (parentA : Nonempty (Derivation body Γ (measureGraph base P x (auxiliaryTerm dom cod fn arg))))
    (parentB : Nonempty (Derivation body Γ (measureGraph base P y (auxiliaryTerm dom cod fn' arg)))) :
    Nonempty (Derivation body Γ (eqn x y)) := by
  apply programCases P ![mf,ma] _
  intro β j Δ common hJ emit
  rw [eqnRelabel]
  simp only [binaryInputsRename] at emit
  have funcA := renameInto functionA j Δ hJ
  have funcB := renameInto functionB j Δ hJ
  have fixed := renameInto argument j Δ hJ
  have left := renameInto parentA j Δ hJ
  have right := renameInto parentB j Δ hJ
  simp only [measureRename,auxiliaryRename] at funcA funcB fixed left right
  exact equalAfterCombination base P (dom.relabel j) (cod.relabel j) (fn.relabel j) (fn'.relabel j)
    (arg.relabel j) (mf.relabel j) (ma.relabel j) common (x.relabel j) (y.relabel j) funcA funcB fixed left right emit

private theorem sameValue (base : Program 1) (P : Program 2)
    (dom cod fn fn' arg m x y : OTerm α)
    (functionA : Nonempty (Derivation body Γ (measureGraph base P m fn)))
    (functionB : Nonempty (Derivation body Γ (measureGraph base P m fn')))
    (parentA : Nonempty (Derivation body Γ (measureGraph base P x (auxiliaryTerm dom cod fn arg))))
    (parentB : Nonempty (Derivation body Γ (measureGraph base P y (auxiliaryTerm dom cod fn' arg)))) :
    Nonempty (Derivation body Γ (eqn x y)) := by
  apply programCases (selectedMeasure (measureUpdate base P)) ![arg] _
  intro β j Δ ma hJ argument
  rw [eqnRelabel]
  simp only [inputsRename] at argument
  have funcA := renameInto functionA j Δ hJ
  have funcB := renameInto functionB j Δ hJ
  have left := renameInto parentA j Δ hJ
  have right := renameInto parentB j Δ hJ
  simp only [measureRename,auxiliaryRename] at funcA funcB left right
  exact equalAfterArgument base P (dom.relabel j) (cod.relabel j) (fn.relabel j) (fn'.relabel j)
    (arg.relabel j) (m.relabel j) ma (x.relabel j) (y.relabel j) funcA funcB argument left right

theorem exact_OpenAuxMeasureEvaluation : ExactOpenAuxMeasureEvaluation := by
  intro base P body α Γ dom cod fn arg mf ma out children emit
  let Δ := (children ⊓ emit) :: Γ
  have facts : Derivation body Δ (children ⊓ emit) := Derivation.hypothesis List.mem_cons_self
  have reports := Derivation.conjunctionLeft facts
  obtain ⟨result⟩ := deriveValue base P dom cod fn arg mf ma out
    ⟨Derivation.conjunctionLeft reports⟩ ⟨Derivation.conjunctionRight reports⟩ ⟨Derivation.conjunctionRight facts⟩
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_OpenAuxMeasureEquality : ExactOpenAuxMeasureEquality := by
  intro base P body α Γ dom cod fn fn' arg m x y children parents
  let Δ := (children ⊓ parents) :: Γ
  have facts : Derivation body Δ (children ⊓ parents) := Derivation.hypothesis List.mem_cons_self
  have functions := Derivation.conjunctionLeft facts
  have applications := Derivation.conjunctionRight facts
  obtain ⟨result⟩ := sameValue base P dom cod fn fn' arg m x y
    ⟨Derivation.conjunctionLeft functions⟩ ⟨Derivation.conjunctionRight functions⟩
    ⟨Derivation.conjunctionLeft applications⟩ ⟨Derivation.conjunctionRight applications⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_OpenAuxMeasureEvaluation
#print axioms exact_OpenAuxMeasureEquality

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenChecks
