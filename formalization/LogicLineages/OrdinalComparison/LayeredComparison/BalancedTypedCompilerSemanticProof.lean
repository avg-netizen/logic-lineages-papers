module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerCallProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
open BalancedSyntax

/-- The recursive comparator uses the actual lower certificate and the same
raw valuation. The lower induction hypothesis asks for positivity only on
each queried pair's support; the accepted guard descent supplies precisely
those local hypotheses from the original upper support. -/
theorem actualSignSemantics : Targets.ActualSignSemantics := by
  classical
  intro Γ
  induction Γ with
  | nil =>
    intro C E F desired ν hC hE hF hpositive
    exact (BalancedRawCompiler.Proof.exactFiniteCallEquation.2.1
      0 E F desired).2 ν
  | cons k Γ ih =>
    intro C E F desired ν hC hE hF hpositive
    have hlower : BalancedGuardDescent.LowerCorrect Γ C.1
        (fun G H d => typedFormula Γ C.1 G H d) ν := by
      intro G H d hG hH hpos
      exact ih C.1 G H d ν hC.1 hG hH hpos
    have hguard := (BalancedGuardDescent.Proof.actualSourceDescent.1
      k Γ C E F desired (fun G H d => typedFormula Γ C.1 G H d)
        ν hC hE hF hpositive hlower).2
    have hbox := BalancedBoxFormula.Proof.exactFiniteBoxFormula.1
      k Γ C E F desired ν
    change ((BalancedBoxFormula.sourceFormula k Γ C E F desired).eval ν ∨
      (BalancedGuardDescent.sourceTranslation k Γ C E F desired
        (fun G H d => typedFormula Γ C.1 G H d)).eval ν) ↔ _
    rw [hbox, hguard]
    constructor
    · rintro (⟨_, hsign⟩ | ⟨_, hsign⟩)
      · exact hsign
      · exact hsign
    · intro hsign
      by_cases hlarge : ∀ a ∈ (comparisonRow E F).atoms,
          BalancedRow.threshold (comparisonRow E F) ≤
            BalancedRow.input (basisValues k Γ C ν) a.2
      · exact Or.inr ⟨hlarge, hsign⟩
      · have hsmall : BalancedSmallBox.smallBranch k Γ C E F ν := by
          by_contra hsmall
          apply hlarge
          intro a ha
          exact Nat.le_of_not_lt (fun hlt => hsmall ⟨a, ha, hlt⟩)
        have hbounds := BalancedSmallBox.Proof.actualSmallInputBounds
          k Γ C E F ν hC hsmall
        exact Or.inl ⟨fun i hi => ⟨hpositive i hi, hbounds.2.2.2 i hi⟩, hsign⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Proof
