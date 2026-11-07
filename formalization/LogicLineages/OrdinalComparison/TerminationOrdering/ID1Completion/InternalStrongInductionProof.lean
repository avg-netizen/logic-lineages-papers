module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalStrongInduction
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open InternalStrongInductionSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The existing classical rule, packaged for a double-negated conclusion. -/
def eliminateDoubleNegation {p : Formula α} (h : Derivation body Gamma p.not.not) :
    Derivation body Gamma p :=
  Derivation.classical (Derivation.implicationElimination
    (addHyp h p.not) (Derivation.hypothesis List.mem_cons_self))

/-- Eliminate double negations under the literal bounded universal. This
uses only the original logical rules, so theta is not restricted to arithmetic. -/
theorem belowDoubleNegation (theta : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    Nonempty (Derivation body []
      ((InternalLeastNumberSyntaxProof.below theta.not t).imp (below theta t))) := by
  let guard := ltF (.var (.inr 0)) (t.relabel (Sum.inl : α → α ⊕ Fin 1))
  have h : Derivation body []
      ((guard.imp theta.not.not).imp (guard.imp theta)) := by
    apply Derivation.implicationIntroduction
    apply Derivation.implicationIntroduction
    apply eliminateDoubleNegation
    exact Derivation.implicationElimination
      (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
      (Derivation.hypothesis List.mem_cons_self)
  exact actualInternalUniversalTransport body α _ _ ⟨h⟩

/-- Classical first-order quantifier duality, as an explicit proof-tree
transformation rather than a semantic completeness principle. -/
theorem allOfNoCounterexample (theta : Formula (α ⊕ Fin 1))
    (h : Nonempty (Derivation body Gamma (existsOne theta.not).not)) :
    Nonempty (Derivation body Gamma (allOne theta)) := by
  let Delta := theta.not :: Gamma.map weaken
  have hi : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hn := renameInto h Sum.inl Delta hi
  change Nonempty (Derivation body Delta ((existsOne theta.not).relabel Sum.inl).not) at hn
  rw [existsRename] at hn
  obtain ⟨hn⟩ := hn
  have hx : Derivation body Delta (existsOne (lift theta.not)) := by
    apply Derivation.existentialIntroduction (emb (.var (.inr 0)))
    rw [freshLift]
    exact Derivation.hypothesis List.mem_cons_self
  have hf : Derivation body Delta (⊥ : Formula (α ⊕ Fin 1)) :=
    Derivation.implicationElimination hn hx
  exact ⟨Derivation.universalIntroduction (Derivation.classical hf)⟩

/-- A least counterexample cannot satisfy progressiveness. The least-number
supplier is itself derived by PA induction in this same expanded language. -/
theorem actualStrongInductionSchema : InternalStrongInductionTargets.ActualStrongInductionSchema := by
  intro body α theta
  let H := allOne (step theta)
  let Gamma := [existsOne theta.not, H]
  let Delta := InternalLeastNumberSyntaxProof.minP theta.not :: Gamma.map weaken
  obtain ⟨least⟩ := InternalLeastNumberProof.leastNumber (body := body) theta.not
  have hm : Derivation body Gamma (existsOne (InternalLeastNumberSyntaxProof.minP theta.not)) :=
    Derivation.implicationElimination (weakenClosed least Gamma)
      (Derivation.hypothesis List.mem_cons_self)
  have hn : Derivation body Delta theta.not :=
    Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
  have hbnn : Derivation body Delta
      (InternalLeastNumberSyntaxProof.below (lift theta).not (.var (.inr 0))) :=
    Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨dne⟩ := belowDoubleNegation (body := body) (lift theta) (.var (.inr 0))
  have hb : Derivation body Delta (below (lift theta) (.var (.inr 0))) :=
    Derivation.implicationElimination (weakenClosed dne Delta) hbnn
  have ha : Derivation body Delta (weaken (allOne (step theta))) :=
    Derivation.hypothesis (by simp [Delta,Gamma,H])
  rw [weaken,actualUniversalRenaming] at ha
  have hs := Derivation.universalElimination (emb (.var (.inr (0 : Fin 1)))) ha
  change Derivation body Delta
    (instantiate (lift (step theta)) (emb (.var (.inr 0)))) at hs
  rw [freshLift] at hs
  have hf : Derivation body Delta (⊥ : Formula (α ⊕ Fin 1)) :=
    Derivation.implicationElimination hn (Derivation.implicationElimination hs hb)
  have contradiction : Derivation body Gamma (⊥ : Formula α) :=
    Derivation.existentialElimination hm hf
  have noCounterexample : Derivation body [H] (existsOne theta.not).not :=
    Derivation.implicationIntroduction contradiction
  obtain ⟨all⟩ := allOfNoCounterexample theta ⟨noCounterexample⟩
  exact ⟨Derivation.implicationIntroduction all⟩

/-- Reusable contextual form; the original context survives unchanged. -/
theorem strongInduction (theta : Formula (α ⊕ Fin 1))
    (h : Nonempty (Derivation body
      (below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta)) :
    Nonempty (Derivation body Gamma (allOne theta)) := by
  obtain ⟨d⟩ := actualStrongInductionSchema body α theta
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed d Gamma)
    (Derivation.universalIntroduction (Derivation.implicationIntroduction h))⟩

theorem actualStrongInductionRule : InternalStrongInductionTargets.ActualStrongInductionRule :=
  fun _ _ _ theta => strongInduction theta

theorem actualStrongInductionInstance : InternalStrongInductionTargets.ActualStrongInductionInstance := by
  intro body α Gamma theta t h
  obtain ⟨d⟩ := strongInduction theta h
  exact ⟨Derivation.universalElimination (emb t) d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
