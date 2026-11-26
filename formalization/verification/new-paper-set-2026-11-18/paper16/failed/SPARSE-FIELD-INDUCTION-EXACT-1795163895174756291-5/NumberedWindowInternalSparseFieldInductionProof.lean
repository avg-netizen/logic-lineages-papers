module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldBranchesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax belowRename freshLift)
open ID1Completion.InternalStrongInductionProof (strongInduction)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (z eqn emb)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparsePairChecks (exact_OpenFieldConsTailDecrease)
open NumberedWindowInternalSparseFieldInductionTargets NumberedWindowInternalSparseFieldBranchesProof
open NumberedWindowInternalSparseFieldExistentialProof NumberedWindowInternalSparseFieldIndexProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consAt (θ : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hP : Nonempty (Derivation body Γ (premises θ)))
    (hB : Nonempty (Derivation body Γ (below θ n)))
    (hC : Nonempty (Derivation body Γ (someCons n))) :
    Nonempty (Derivation body Γ (atCode θ n)) := by
  apply someConsCases n (atCode θ n) hC
  intro β j Δ hd tl hJ hc
  rw [atCodeRename]
  let θ' := θ.relabel (Sum.map j id)
  let nn := n.relabel j
  have hp' := renameInto hP j Δ hJ
  rw [premisesRename] at hp'
  have hb' := renameInto hB j Δ hJ
  rw [belowRename] at hb'
  obtain ⟨hb'⟩ := hb'
  have small := Derivation.universalElimination (emb tl) hb'
  rw [belowElimSyntax] at small
  obtain ⟨ordered⟩ := closedApply (exact_OpenFieldConsTailDecrease body β nn hd tl) hc
  have tail : Nonempty (Derivation body Δ (atCode θ' tl)) :=
    ⟨Derivation.implicationElimination small (Derivation.conjunctionRight ordered)⟩
  obtain ⟨hp'⟩ := hp'
  exact consApply θ' nn hd tl ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hp')⟩ hc tail

private theorem nonzeroAt (θ : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hp : Nonempty (Derivation body Γ (premises θ)))
    (hb : Nonempty (Derivation body Γ (below θ n)))
    (hn : Nonempty (Derivation body Γ (nonzero n))) :
    Nonempty (Derivation body Γ (atCode θ n)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hb⟩ := hb
  obtain ⟨hn⟩ := hn
  let p := someCons n
  obtain ⟨yes⟩ := consAt (Γ := p :: Γ) θ n ⟨addHyp hp p⟩ ⟨addHyp hb p⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have bad : Derivation body (p.not :: Γ) (malformed n) :=
    Derivation.conjunctionIntroduction (addHyp hn p.not) (Derivation.hypothesis List.mem_cons_self)
  have g := Derivation.conjunctionLeft (Derivation.conjunctionRight (addHyp hp p.not))
  obtain ⟨no⟩ := gapApply θ n ⟨g⟩ ⟨bad⟩
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

private theorem stepAt (θ : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (hp : Nonempty (Derivation body Γ (premises θ)))
    (hb : Nonempty (Derivation body Γ (below θ n))) :
    Nonempty (Derivation body Γ (atCode θ n)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hb⟩ := hb
  let p := eqn n z
  have nil : Derivation body (p :: Γ) (atCode θ n) := by
    have e : Derivation body (p :: Γ) (eqn n z) := Derivation.hypothesis List.mem_cons_self
    exact Derivation.equalityElimination θ (emb z) (emb n) (symm e) (Derivation.conjunctionLeft (addHyp hp p))
  have nz : Derivation body (p.not :: Γ) (nonzero n) := by
    rw [nonzero,equalEqn]
    exact Derivation.hypothesis List.mem_cons_self
  obtain ⟨other⟩ := nonzeroAt θ n ⟨addHyp hp p.not⟩ ⟨addHyp hb p.not⟩ ⟨nz⟩
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction nil) (Derivation.implicationIntroduction other)⟩

theorem schema : SparseFieldInductionSchema := by
  intro body α θ
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := below (lift θ) x :: ([premises θ] : List (Formula α)).map weaken
  have hp : Nonempty (Derivation body Δ (premises (lift θ))) := by
    have old : Derivation body Δ (weaken (premises θ)) := Derivation.hypothesis (by simp [Δ])
    change Derivation body Δ ((premises θ).relabel Sum.inl) at old
    rw [premisesRename] at old
    exact ⟨old⟩
  have hb : Nonempty (Derivation body Δ (below (lift θ) x)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step := stepAt (lift θ) x hp hb
  change Nonempty (Derivation body Δ (instantiate (lift θ) (emb (.var (.inr 0))))) at step
  rw [freshLift] at step
  obtain ⟨all⟩ := strongInduction (Gamma := [premises θ]) θ step
  exact ⟨Derivation.implicationIntroduction all⟩

theorem atTerm : SparseFieldInductionAtCode := by
  intro body α Γ θ n hp
  obtain ⟨all⟩ := closedApply (schema body α θ) hp
  exact ⟨Derivation.universalElimination (emb n) all⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionProof
