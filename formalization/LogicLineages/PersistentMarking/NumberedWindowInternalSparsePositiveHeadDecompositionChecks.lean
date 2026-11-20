module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePairChecks (exact_OpenFieldConsTailDecrease)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof (toPositive)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof (forward)

private theorem acceptData {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source cert target hd tl next : OTerm α)
    (data : Nonempty (Derivation body Γ (headData raw least ctx ty source cert target hd tl next))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target)) := by
  obtain ⟨d⟩ := data
  have head : Nonempty (Derivation body Γ (genuineHead raw least ctx ty (suc source) cert hd tl (suc next))) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft d)
      (Derivation.conjunctionLeft (Derivation.conjunctionRight d))⟩
  obtain ⟨equiv⟩ := closedApply (exact_OpenFinishCons body raw least α (suc target) ctx ty (suc source)
    cert hd tl (suc next)) head
  let rest := Derivation.conjunctionRight (Derivation.conjunctionRight d)
  have all := Derivation.implicationElimination (Derivation.conjunctionRight equiv) rest
  obtain ⟨bounds⟩ := closedApply (exact_OpenFieldConsTailDecrease body α cert hd tl)
    ⟨Derivation.conjunctionLeft d⟩
  exact toPositive raw least ctx ty source cert target ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft bounds) all⟩

private theorem backward {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (known : Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target)) := by
  apply headCases raw least ctx ty source cert target (positiveAt raw least ctx ty source cert target) known
  intro β j Δ hd tl next _ data
  rw [positiveRename]
  exact acceptData raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
    (target.relabel j) hd tl next data

theorem exact_OpenPositiveFinish : OpenPositiveFinish :=
  NumberedWindowInternalSparsePositiveHeadDecompositionFinishChecks.exact_OpenPositiveFinish

theorem exact_OpenPositiveHeadDecomposition : OpenPositiveHeadDecomposition := by
  intro body raw least α ctx ty source cert target
  let a := positiveAt raw least ctx ty source cert target
  let b := hasAcceptedHead raw least ctx ty source cert target
  obtain ⟨f⟩ := forward (body := body) (Γ := [a]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := backward (body := body) (Γ := [b]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

#print axioms exact_OpenPositiveFinish
#print axioms exact_OpenPositiveHeadDecomposition
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
