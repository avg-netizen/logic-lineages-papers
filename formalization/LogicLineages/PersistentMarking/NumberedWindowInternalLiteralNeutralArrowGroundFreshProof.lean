module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralFreeArrowGroundCheckedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundFreshProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt freshAt)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports sourceShape)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_OpenLiteralParsedFresh)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalLiteralNeutralFreeArrowGroundCheckedProof
  (exact_OpenLiteralNeutralFreeArrowGroundCChecked)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution)

private theorem renameFormula {α β : Type} (p : Program 3) (τ : ProbeTy) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

/-- The actual given fresh u at an arbitrary arrow-into-ground domain is
computable. The source reports use exactly the supplied v, the conclusion
uses exactly the physical shape/output guarded p. No parser reselection,
numeric transfer, or same-guard identity is inferred. -/
theorem exact_OpenLiteralNeutralArrowGroundFresh
    (i : Program 1) (r p : Program 3) (c : Nat)
    (v : Inputs) (W : List ProbeTy) (σ τ : ProbeTy) (α : Type) (Γ : List (Formula α))
    (q u : OTerm α)
    (typed : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (typedAt (chosenH v W) (.arrow (.arrow σ .ground) τ) q)))
    (fresh : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (freshAt (chosenA v) q u))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (formula (outputGuard i (refinedApplication p)) (.arrow σ .ground) u)) := by
  let B := sourceBody (literalNeutral i r) c
  let P := outputGuard i (refinedApplication p)
  let β := α ⊕ Fin 6
  let j : α → β := Sum.inl
  let ctx : OTerm β := .var (.inr 0)
  let res : OTerm β := .var (.inr 1)
  let d : OTerm β := .var (.inr 2)
  let e : OTerm β := .var (.inr 3)
  let raw : OTerm β := .var (.inr 4)
  let name : OTerm β := .var (.inr 5)
  let q' := q.relabel j
  let u' := u.relabel j
  let matrix := addressReports q' ctx res raw ⊓ (arrowReports q' d e ⊓
    (sourceShape q' ctx res d e raw ⊓ (programGraph v.freshBound name ![raw] ⊓
      (equal u' (packedFreeTerm ctx d name) ⊓
        (equal d (numeral (typeCode (.arrow σ .ground))) ⊓ equal e (numeral (typeCode τ)))))))
  have original := exact_OpenLiteralParsedFresh v W (.arrow σ .ground) τ B α Γ q u typed fresh
  apply actualFiniteExistentialElimination B α 6 Γ matrix (formula P (.arrow σ .ground) u) original
  let Δ := matrix :: Γ.map (fun f => f.relabel j)
  have facts : Derivation B Δ matrix := Derivation.hypothesis List.mem_cons_self
  have tail := Derivation.conjunctionRight (Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight facts)))
  rw [renameFormula]
  exact exact_OpenLiteralNeutralFreeArrowGroundCChecked i r p c σ β Δ u' ctx d name
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight tail)⟩
    ⟨Derivation.conjunctionLeft tail⟩

#print axioms exact_OpenLiteralNeutralArrowGroundFresh
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundFreshProof
