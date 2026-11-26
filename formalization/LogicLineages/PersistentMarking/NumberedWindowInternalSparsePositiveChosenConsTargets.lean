module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveFold (chosenState finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 equivalent)

/-- The actual leading sparse polynomial cell and the actual selected
advance for its head at unchanged context/type. Encoded current and
advanced current may be zero (rejection), and the raw tail may be nil.
Neither a nonempty tail nor callback acceptance is an assumption. -/
def genuineHead {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current certificate head tail next : OTerm α) : Formula α :=
  consGraph certificate head tail ⊓ selectedGraph raw least next ctx ty current head

/-- The two chosen-state computations use their own actual raw codes as
fuel. They return the same genuine scratch state when the original
leading hop has been processed. No common chosen numerical fuel or
external sufficient-fuel premise is supplied. -/
def OpenChosenStateCons : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out ctx ty current certificate head tail next : OTerm α),
    let h := genuineHead raw least ctx ty current certificate head tail next
    let a := programGraph (chosenState raw least) out (args4 ctx ty current certificate)
    let b := programGraph (chosenState raw least) out (args4 ctx ty next tail)
    Nonempty (Derivation body [] (h.imp (equivalent a b)))

/-- Actual chosen-fuel finish obeys that same head/tail recurrence for
the literal encoded current, including none0 and a nil tail. -/
def OpenFinishCons : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out ctx ty current certificate head tail next : OTerm α),
    let h := genuineHead raw least ctx ty current certificate head tail next
    let a := programGraph (finish raw least) out (args4 ctx ty current certificate)
    let b := programGraph (finish raw least) out (args4 ctx ty next tail)
    Nonempty (Derivation body [] (h.imp (equivalent a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsTargets
