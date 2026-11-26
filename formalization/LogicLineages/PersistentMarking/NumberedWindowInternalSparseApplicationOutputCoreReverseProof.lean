module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreCallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReverseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseApplicationOutputCore
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape)
open NumberedWindowInternalSparseApplicationOutputCoreCallProof (selectGraph comparison)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (tapeRename auxiliaryRename reportUnfold reportBinder)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rebuild (least : Program 3) (ctx dom cod fn arg y : OTerm α)
    (supplied : Nonempty (Derivation body Γ (outputReport least ctx cod
      (auxiliaryTerm dom cod fn arg) y))) :
    Nonempty (Derivation body Γ (programGraph (outputCore least) (suc z)
      (objectTape ctx dom cod fn arg y))) := by
  rw [reportUnfold] at supplied
  obtain ⟨report⟩ := supplied
  let A := reportBinder least ctx cod (auxiliaryTerm dom cod fn arg) y
  let Δ := A :: Γ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let c := ctx.relabel j
  let d := dom.relabel j
  let t := cod.relabel j
  let f := fn.relabel j
  let a := arg.relabel j
  let out := y.relabel j
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let xs := objectTape c d t f a out
  have suppliedIn : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have actual : Nonempty (Derivation body Δ
      (programGraph least (suc k) ![c,t,(auxiliaryTerm dom cod fn arg).relabel j])) :=
    ⟨Derivation.conjunctionLeft suppliedIn⟩
  rw [auxiliaryRename] at actual
  have control := selectGraph least (suc k) c d t f a out actual
  have yes := (comparison least k c d t f a out control).mpr
    ⟨Derivation.conjunctionRight suppliedIn⟩
  obtain ⟨newGraph⟩ := successorBranchIntro (selectedLeast least) (constantZero 6)
    (compareOutput least) (suc z) k xs control yes
  have branchResult : Derivation body Δ (weaken (programGraph (outputCore least) (suc z)
      (objectTape ctx dom cod fn arg y))) := by
    change Derivation body Δ ((programGraph (outputCore least) (suc z)
      (objectTape ctx dom cod fn arg y)).relabel j)
    rw [programRename,tapeRename,sucRelabel,zRelabel]
    exact newGraph
  exact ⟨Derivation.existentialElimination report branchResult⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReverseProof
