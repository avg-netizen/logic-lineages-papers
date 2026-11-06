module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityFiberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof SourceComputabilityFormulaProof
open NumberedLeastCodeRepresentative JointGammaComputability

theorem typedTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (hcal : Calibrated data n arity)
    (context typ x : Nat) :
    (JointGammaTyped.typedFormula data.typed).Realize ![context,typ,x] ↔ JointGammaTyped.encodedTyped n arity context typ x := by
  rw [JointGammaTyped.typedFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hcal.1]
  exact JointGammaTypedProof.calibration n arity context typ x

theorem guardTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (hcal : Calibrated data n arity)
    (f a : Nat) :
    (SourcePresentation.checkerFormula data.guard).Realize ![f,a] ↔ JointGammaDomain.sameContext f a := by
  rw [SourcePresentation.checkerFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hcal.2.1]
  exact JointGammaDomainProof.actualGuardCalibration.1 f a

theorem appTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (hcal : Calibrated data n arity)
    (context domain codomain f a z : Nat) :
    (JointGammaApplication.applicationFormula data.application).Realize ![context,domain,codomain,f,a,z] ↔
      JointGammaApplication.encodedApplication n arity context domain codomain f a z := by
  rw [JointGammaApplication.applicationFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hcal.2.2]
  exact JointGammaApplicationProof.calibration n arity context domain codomain f a z

theorem guardAtTruth (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 2)
    (P : Nat → Prop) (context x : Nat) (us : Fin 1 → Nat) :
    realize P (guardAt p) (Sum.elim ![context,x] us) ↔
      (SourcePresentation.checkerFormula p).Realize ![x,us 0] := by
  unfold guardAt
  rw [arithmeticSubstTruth]
  have hv : (fun i : Fin 2 =>
      (![(.var (.inl 1) : OrdinaryArithmetic.Term (Fin 2 ⊕ Fin 1)),.var (.inr 0)] i).realize
        (Sum.elim ![context,x] us)) = ![x,us 0] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [hv]

theorem actualFormulaCalibration : JointGammaComputabilityTargets.ActualFormulaCalibration := by
  intro data n arity hcal tau
  induction tau with
  | ground =>
    intro P context x
    rw [formula,generalConjTruth,typedAtTruth,typedTruth data n arity hcal,
      predicateTruth,PositiveArithmeticTransformsProof.tagTermTruth]
    rfl
  | arrow sigma tau ihs iht =>
    intro P context x
    have hdom (us : Fin 1 → Nat) :
        realize P ((formula data sigma).relabel ![.inl 0,.inr 0]) (Sum.elim ![context,x] us) ↔
          Computable n arity P context sigma (us 0) := by
      rw [generalRelabelTruth]
      have hv : (Sum.elim ![context,x] us) ∘ ![Sum.inl 0,Sum.inr 0] = ![context,us 0] := by
        funext i
        exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
      rw [hv]
      exact ihs P context (us 0)
    have hcod (us zs : Fin 1 → Nat) :
        realize P ((formula data tau).relabel ![.inl (.inl 0),.inr 0])
          (Sum.elim (Sum.elim ![context,x] us) zs) ↔ Computable n arity P context tau (zs 0) := by
      rw [generalRelabelTruth]
      have hv : (Sum.elim (Sum.elim ![context,x] us) zs) ∘ ![Sum.inl (Sum.inl 0),Sum.inr 0] =
          ![context,zs 0] := by
        funext i
        exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
      rw [hv]
      exact iht P context (zs 0)
    rw [formula,generalConjTruth,typedAtTruth,typedTruth data n arity hcal,allOneTruth]
    simp only [generalImpTruth,guardAtTruth,guardTruth data n arity hcal,hdom,existsOneTruth,
      generalConjTruth,appAtTruth,appTruth data n arity hcal,hcod]
    change (_ ∧ ∀ us : Fin 1 → Nat, _ → _ → ∃ zs : Fin 1 → Nat, _) ↔
      (_ ∧ ∀ u : Nat, _ → _ → ∃ z : Nat, _)
    constructor
    · rintro ⟨hc,h⟩
      refine ⟨hc,?_⟩
      intro u hs hu
      obtain ⟨zs,hz⟩ := h (fun _ => u) hs hu
      exact ⟨zs 0,hz⟩
    · rintro ⟨hc,h⟩
      refine ⟨hc,?_⟩
      intro us hs hu
      obtain ⟨z,hz⟩ := h (us 0) hs hu
      exact ⟨fun _ => z,hz⟩

theorem actualFiniteWindowCalibration : JointGammaComputabilityTargets.ActualFiniteWindowCalibration := by
  intro data n arity hcal S P context typ x
  rw [SourceFiniteComputabilityFormulaProof.actualFiniteFormulaAssembly]
  exact exists_congr (fun tau => and_congr_right (fun _ => and_congr_right
    (fun _ => actualFormulaCalibration data n arity hcal tau P context x)))

theorem actualUniformFormulasExist : JointGammaComputabilityTargets.ActualUniformFormulasExist := by
  intro n arity
  obtain ⟨pt,hpt,_,_⟩ := JointGammaTypedProof.actualTypedArithmeticFormula n arity
  obtain ⟨pg,hpg,_⟩ := JointGammaDomainProof.actualGuardArithmeticFormula
  obtain ⟨pa,hpa,_,_⟩ := JointGammaApplicationProof.actualApplicationArithmeticFormula n arity
  let data : Data := ⟨pt,pg,pa⟩
  have hcal : Calibrated data n arity := ⟨hpt,hpg,hpa⟩
  refine ⟨data,hcal,?_,?_⟩
  · intro tau P context Gamma x
    exact (actualFormulaCalibration data n arity hcal tau P context _).trans
      (JointGammaComputabilityFiberProof.actualOriginalComputabilityFibers n arity Gamma P context tau x)
  · intro S P context typ Gamma x
    rw [actualFiniteWindowCalibration data n arity hcal]
    exact exists_congr (fun tau => and_congr_right (fun _ => and_congr_right
      (fun _ => JointGammaComputabilityFiberProof.actualOriginalComputabilityFibers n arity Gamma P context tau x)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
