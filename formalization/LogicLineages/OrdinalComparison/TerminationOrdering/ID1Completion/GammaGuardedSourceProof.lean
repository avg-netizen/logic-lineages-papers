module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open GammaGuardedSource GammaGuardedSourceCalibrationProof GammaGuardedSourceRelationProof
open GuardedSourceGround GuardedSourceGroundProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Explicit normalized Programs choose ONE shared package. Typed and ground
closure are reconstructed for these witnesses, never borrowed from an unrelated
existential package. The arbitrary-context guard clause needs no closed window. -/
theorem actualUniformGuardClosureExists : GammaGuardedSourceTargets.ActualUniformGuardClosureExists := by
  intro n arity
  obtain ⟨oldSource,hs⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  obtain ⟨oldComp,hc,_,_⟩ := JointGammaComputabilityProof.actualUniformFormulasExist n arity
  obtain ⟨gamma,hgamma⟩ := GammaGuardCalibrationProof.actualGammaProgram
  obtain ⟨tag,htag⟩ := GuardCalibrationProof.actualTypeTagProgram
  obtain ⟨window,hwindow⟩ := GuardCalibrationProof.actualValidWindowProgram n
  let valid := GammaGuardCalibration.validity oldComp.guard
  have hvalid := GammaGuardCalibrationProof.actualValidityCalibration oldComp.guard hc.2.1
  obtain ⟨hbs,hbc⟩ := actualBaseCalibration n arity oldSource oldComp valid gamma hs hc hvalid hgamma
  obtain ⟨hs',hc'⟩ := GuardedSourceCalibrationProof.actualGuardedCalibration n arity
    (baseSource oldSource gamma) (baseComputability oldComp valid gamma) tag window hbs hbc htag hwindow
  let src := source oldSource oldComp.typed valid gamma tag window
  let comp := computability oldComp valid gamma tag
  refine ⟨src,comp,hs',hc',?_,?_⟩
  · intro symbols S table hclosed α
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    have hw : evaluate window (List.Vector.ofFn ![context]) = 1 := by
      rw [hwindow]
      exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hclosed
    have htyped : ∀ (typ x y : OrdinaryArithmetic.Term α),
        Nonempty (Derivation (SourcePresentation.sourceBody src context) []
          ((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y).imp
            (GuardedSource.literalTyped comp context typ y))) := by
      intro typ x y
      let P := GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y
      obtain ⟨d⟩ := GuardedSourceRelationProof.relationClosure
        (body := SourcePresentation.sourceBody src context) (Gamma := [P])
        (baseSource oldSource gamma) (baseComputability oldComp valid gamma) tag window context hw typ x y
        ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
        ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
      exact ⟨Derivation.implicationIntroduction d⟩
    refine ⟨htyped,?_⟩
    intro x y
    change Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      ((GuardedSource.literalComputable comp context .ground x ⊓ GuardedSource.literalR src context x y).imp
        (GuardedSource.literalComputable comp context .ground y)))
    rw [groundFormula comp context α x,groundFormula comp context α y]
    obtain ⟨dt⟩ := htyped (numeral (typeNumber .ground)) x y
    obtain ⟨ds⟩ := scalarDownward src context α x y
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have hp := Derivation.hypothesis (body := SourcePresentation.sourceBody src context)
      (show ((GuardedSource.literalTyped comp context (numeral (typeNumber .ground)) x ⊓ literalGround x) ⊓
        GuardedSource.literalR src context x y) ∈
        [((GuardedSource.literalTyped comp context (numeral (typeNumber .ground)) x ⊓ literalGround x) ⊓
          GuardedSource.literalR src context x y)] from List.mem_cons_self)
    have htx := Derivation.conjunctionLeft (Derivation.conjunctionLeft hp)
    have hgx := Derivation.conjunctionRight (Derivation.conjunctionLeft hp)
    have hr := Derivation.conjunctionRight hp
    exact Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (weakenClosed dt _)
        (Derivation.conjunctionIntroduction htx hr))
      (Derivation.implicationElimination (weakenClosed ds _)
        (Derivation.conjunctionIntroduction hgx hr))
  · intro context α typ x y u
    exact actualOriginalGuardTransport oldSource oldComp valid gamma tag window context α typ x y u

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceProof
