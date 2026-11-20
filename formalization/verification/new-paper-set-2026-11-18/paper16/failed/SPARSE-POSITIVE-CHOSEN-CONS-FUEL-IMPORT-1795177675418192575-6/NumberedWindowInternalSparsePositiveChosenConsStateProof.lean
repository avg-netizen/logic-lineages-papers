module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsLoopCompareProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsStateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (chosenState)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveOutputStateProof (loopOfState)
open NumberedWindowInternalSparsePositiveChosenConsTargets
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
open NumberedWindowInternalSparsePositiveChosenConsLoopCompareProof (compareLoops)

attribute [local irreducible] programGraph chosenState

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem compareChosen (raw : Program 5) (least : Program 3)
    (left right ctx ty current cert hd tl next : OTerm α)
    (fact : Nonempty (Derivation body Γ (genuineHead raw least ctx ty current cert hd tl next)))
    (old : Nonempty (Derivation body Γ (chosenGraph raw least left ctx ty current cert)))
    (new : Nonempty (Derivation body Γ (chosenGraph raw least right ctx ty next tl))) :
    Nonempty (Derivation body Γ (eqn left right)) := by
  obtain ⟨fact⟩ := fact
  exact compareLoops raw least left right ctx ty current cert hd tl next
    (loopOfState raw least left ctx ty current cert old) (loopOfState raw least right ctx ty next tl new)
    ⟨Derivation.conjunctionLeft fact⟩ ⟨Derivation.conjunctionRight fact⟩

theorem forward (raw : Program 5) (least : Program 3) (out ctx ty current cert hd tl next : OTerm α)
    (fact : Nonempty (Derivation body Γ (genuineHead raw least ctx ty current cert hd tl next)))
    (old : Nonempty (Derivation body Γ (chosenGraph raw least out ctx ty current cert))) :
    Nonempty (Derivation body Γ (chosenGraph raw least out ctx ty next tl)) := by
  apply chosenCases raw least ctx ty next tl (chosenGraph raw least out ctx ty next tl)
  intro β j Δ other hJ new
  rw [chosenRename]
  have earlier := renameInto old j Δ hJ
  rw [chosenRename] at earlier
  have head := renameInto fact j Δ hJ
  rw [headRename] at head
  obtain ⟨same⟩ := compareChosen raw least (out.relabel j) other (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) (next.relabel j) head earlier new
  exact outputTransport (chosenState raw least) other (out.relabel j)
    (args4 (ctx.relabel j) (ty.relabel j) (next.relabel j) (tl.relabel j)) ⟨symm same⟩ new

theorem backward (raw : Program 5) (least : Program 3) (out ctx ty current cert hd tl next : OTerm α)
    (fact : Nonempty (Derivation body Γ (genuineHead raw least ctx ty current cert hd tl next)))
    (new : Nonempty (Derivation body Γ (chosenGraph raw least out ctx ty next tl))) :
    Nonempty (Derivation body Γ (chosenGraph raw least out ctx ty current cert)) := by
  apply chosenCases raw least ctx ty current cert (chosenGraph raw least out ctx ty current cert)
  intro β j Δ other hJ old
  rw [chosenRename]
  have later := renameInto new j Δ hJ
  rw [chosenRename] at later
  have head := renameInto fact j Δ hJ
  rw [headRename] at head
  have same := compareChosen raw least other (out.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) (next.relabel j) head old later
  exact outputTransport (chosenState raw least) other (out.relabel j)
    (args4 (ctx.relabel j) (ty.relabel j) (current.relabel j) (cert.relabel j)) same old

theorem stateCons : OpenChosenStateCons := by
  intro body raw least α out ctx ty current cert hd tl next
  let h := genuineHead raw least ctx ty current cert hd tl next
  let a := chosenGraph raw least out ctx ty current cert
  let b := chosenGraph raw least out ctx ty next tl
  have fact : Derivation body [h] h := Derivation.hypothesis List.mem_cons_self
  obtain ⟨f⟩ := forward (Γ := [a,h]) raw least out ctx ty current cert hd tl next
    ⟨addHyp fact a⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨g⟩ := backward (Γ := [b,h]) raw least out ctx ty current cert hd tl next
    ⟨addHyp fact b⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction f) (Derivation.implicationIntroduction g))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsStateProof
