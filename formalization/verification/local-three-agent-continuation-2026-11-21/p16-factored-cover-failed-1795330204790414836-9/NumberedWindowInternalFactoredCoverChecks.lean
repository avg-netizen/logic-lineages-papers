module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape callbackAt)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (callbackFromOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalFactoredCoverTargets
open NumberedWindowInternalFactoredCoverNumericProof (calibration selected invariance)

theorem exact_FactoredCoverCalibration : ExactFactoredCoverCalibration := calibration

theorem exact_SelectedFactoredCover : ExactSelectedFactoredCover := selected

theorem exact_MeasureExchangeInvariance : ExactMeasureExchangeInvariance := invariance

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rawReport (p : Program 1) (s : Settings) (out seed : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out seed))) :
    Nonempty (Derivation body Γ (programGraph (rawCall p) out (callbackTape s seed))) := by
  apply compositionValue p (fun _ : Fin 1 => .projection (2 : Fin 3)) out (callbackTape s seed) ![seed] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) (callbackTape s seed)

private def boundTape {α : Type} (s : Settings) (m : OTerm α) : Fin 3 → OTerm α :=
  ![numeral (Encodable.encode s.window.2),numeral (Encodable.encode s.types),m]

private theorem grammarReport (V M : Program 1) (G : Program 3) (s : Settings) (out seed m : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) seed)))
    (bounds : Nonempty (Derivation body Γ (unary M m seed)))
    (covered : Nonempty (Derivation body Γ (unary (coverOption (factoredCover V M G) s) out seed))) :
    Nonempty (Derivation body Γ (programGraph G out (boundTape s m))) := by
  let args := callbackTape s seed
  let selected := callbackFromOption (factoredCover V M G) s out seed covered
  have generator := successorBranchElim (rawCall V) (constantZero 3) (generatorCall M G)
    out z args (rawReport V s (suc z) seed valid) selected
  apply compositionRecover G
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall M) Fin.elim0)))
    out args (boundTape s m) generator
  intro i
  exact Fin.cases (projectionValue 0 args) (Fin.cases (projectionValue 1 args)
    (Fin.cases (rawReport M s m seed bounds) (fun k => Fin.elim0 k))) i

theorem exact_OpenFactoredCoverEquality : ExactOpenFactoredCoverEquality := by
  intro V M G s body α Γ a b m x y C inputs outputs
  let Δ := (inputs ⊓ outputs) :: Γ
  have reports : Derivation body Δ (inputs ⊓ outputs) := Derivation.hypothesis List.mem_cons_self
  have args := Derivation.conjunctionLeft reports
  have valid := Derivation.conjunctionLeft args
  have measures := Derivation.conjunctionRight args
  have covers := Derivation.conjunctionRight reports
  have left := grammarReport V M G s x a m ⟨Derivation.conjunctionLeft valid⟩
    ⟨Derivation.conjunctionLeft measures⟩ ⟨Derivation.conjunctionLeft covers⟩
  have right := grammarReport V M G s y b m ⟨Derivation.conjunctionRight valid⟩
    ⟨Derivation.conjunctionRight measures⟩ ⟨Derivation.conjunctionRight covers⟩
  obtain ⟨same⟩ := valueUnique G x y (boundTape s m) left right
  exact ⟨Derivation.implicationIntroduction same⟩

#print axioms exact_FactoredCoverCalibration
#print axioms exact_SelectedFactoredCover
#print axioms exact_MeasureExchangeInvariance
#print axioms exact_OpenFactoredCoverEquality

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverChecks
