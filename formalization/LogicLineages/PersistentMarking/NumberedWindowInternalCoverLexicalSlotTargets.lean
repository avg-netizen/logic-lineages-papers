module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction branch constantZero)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldCell (cellTail cellGood cellHead)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)

/-- Recursor tape [counter,previous sparse context,initial sparse context]. -/
def dropTail : Program 3 := .composition cellTail (fun _ : Fin 1 => .projection 1)
def dropStep : Program 3 := branch (.projection 1) (constantZero 3) dropTail

/-- Input [index, original sparse lexical context]; no standard-list lookup. -/
def dropContext : Program 2 := .recursion (.projection 0) dropStep

/-- Input [index, original sparse lexical context, expected type]. -/
def dropped : Program 3 := reorder dropContext ![0,1]
def inhabited : Program 3 := .composition cellGood (fun _ : Fin 1 => dropped)
def atType : Program 3 := .composition cellHead (fun _ : Fin 1 => dropped)
def slotCheck : Program 3 := conjunction inhabited (binary equalityTest atType (.projection 2))

abbrev SlotReports {α : Type} (body : Positive (Fin 1)) (Γ : List (Formula α))
    (i ctx ty rest : OTerm α) : Prop :=
  Nonempty (Derivation body Γ (programGraph dropContext rest ![i,ctx])) ∧
  Nonempty (Derivation body Γ (unary cellGood (suc z) rest)) ∧
  Nonempty (Derivation body Γ (unary cellHead ty rest))

def ExactCoverPhysicalContextDrop : Prop :=
  ∀ i (g : List Nat), evaluate dropContext (i ::ᵥ pack g ::ᵥ nil) = pack (g.drop i)

/-- A calibrated successful original lexical index read is accepted by the
physical sparse guard, including type zero only when a cell actually exists. -/
def ExactCoverPhysicalLexicalSlot : Prop :=
  ∀ (g : List Nat) (i ty : Nat), g[i]? = some ty →
    evaluate slotCheck (i ::ᵥ pack g ::ᵥ ty ::ᵥ nil) = 1

/-- Recover a single actual suffix witnessing its good cell and actual type
at exactly the original context and index. No host-list decoding is used. -/
def ExactOpenCoverPhysicalLexicalSlot : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (i ctx ty : OTerm α)
    (Q : Formula α),
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (rest : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      SlotReports body Δ (i.relabel j) (ctx.relabel j) (ty.relabel j) rest →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotTargets
