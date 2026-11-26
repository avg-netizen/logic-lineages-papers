module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords quadRename coordsRename)
open NumberedWindowInternalSparsePositiveFold (chosenState finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 equivalent)
open NumberedWindowInternalSparsePositiveChosenConsTargets

attribute [local irreducible] programGraph chosenState finish advance

def chosenGraph {α : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert : OTerm α) : Formula α :=
  programGraph (chosenState raw least) out (args4 ctx ty current cert)

def finishGraph {α : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert : OTerm α) : Formula α :=
  programGraph (finish raw least) out (args4 ctx ty current cert)

theorem headRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current cert hd tl next : OTerm α) (j : α → β) :
    (genuineHead raw least ctx ty current cert hd tl next).relabel j =
      genuineHead raw least (ctx.relabel j) (ty.relabel j) (current.relabel j) (cert.relabel j)
        (hd.relabel j) (tl.relabel j) (next.relabel j) := by
  unfold genuineHead selectedGraph
  rw [conjunctionRename,consGraphRename,quadRename]

theorem chosenRename {α β : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert : OTerm α) (j : α → β) :
    (chosenGraph raw least out ctx ty current cert).relabel j =
      chosenGraph raw least (out.relabel j) (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (cert.relabel j) :=
  quadRename (chosenState raw least) out ctx ty current cert j

theorem finishRename {α β : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert : OTerm α) (j : α → β) :
    (finishGraph raw least out ctx ty current cert).relabel j =
      finishGraph raw least (out.relabel j) (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (cert.relabel j) :=
  quadRename (finish raw least) out ctx ty current cert j

theorem finishEquivalenceRename {α β : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert next tail : OTerm α) (j : α → β) :
    (equivalent (finishGraph raw least out ctx ty current cert)
      (finishGraph raw least out ctx ty next tail)).relabel j =
    equivalent (finishGraph raw least (out.relabel j) (ctx.relabel j) (ty.relabel j)
      (current.relabel j) (cert.relabel j)) (finishGraph raw least (out.relabel j)
        (ctx.relabel j) (ty.relabel j) (next.relabel j) (tail.relabel j)) := by
  let a := finishGraph raw least out ctx ty current cert
  let b := finishGraph raw least out ctx ty next tail
  change ((a.relabel j).imp (b.relabel j)) ⊓ ((b.relabel j).imp (a.relabel j)) = _
  simp only [a,b,finishRename,equivalent]

theorem chosenCases {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty current cert : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (chosenGraph raw least out (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (cert.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases (chosenState raw least) (coords ctx ty current cert) goal
  intro β j Δ out hJ known
  rw [coordsRename] at known
  exact k β j Δ out hJ known

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
