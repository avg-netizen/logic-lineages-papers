module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalChosenAuxMeasureCombine (callOne callTwo maximum predecessorDepth numeralBound)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

/-- [literal stored numeral, actual prefix measure, actual suffix measure]. -/
def numberedPredDepth : Program 3 := reorder predecessorDepth ![1,2]
def numberedChildMax : Program 3 := reorder numeralBound ![1,2]
def numberedWidth : Program 3 := callTwo maximum (.projection 0) numberedChildMax
def numberedJoin : Program 3 :=
  callTwo ID1Completion.InternalPairing.pairing (callOne .succ numberedPredDepth) numberedWidth

def ExactCoverNumberedJoin : Prop := ∀ id l r wl wr : Nat,
  evaluate numberedJoin (id ::ᵥ Encodable.encode (l,wl) ::ᵥ Encodable.encode (r,wr) ::ᵥ nil) =
    Encodable.encode (l+r+1,max id (max wl wr))

/-- The same observed real max report bounds both actual operands. -/
def ExactOpenCoverMaximumWeak : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (a b w : OTerm α),
    Nonempty (Derivation body Γ (programGraph maximum w ![a,b])) →
    Nonempty (Derivation body Γ (ltF a (suc w) ⊓ ltF b (suc w)))

structure NumberedJoinBounds (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p k dl dr wl wr width : OTerm α) : Prop where
  parent : Nonempty (Derivation body Γ (codePair p (suc (add dl dr)) width))
  leftDepth : Nonempty (Derivation body Γ (ltF dl (suc (add dl dr))))
  rightDepth : Nonempty (Derivation body Γ (ltF dr (suc (add dl dr))))
  leftWidth : Nonempty (Derivation body Γ (ltF wl (suc width)))
  rightWidth : Nonempty (Derivation body Γ (ltF wr (suc width)))
  storedNumeral : Nonempty (Derivation body Γ (ltF k (suc width)))

def ExactOpenCoverNumberedJoin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p k ml mr dl dr wl wr mid width : OTerm α),
    Nonempty (Derivation body Γ (codePair ml dl wl)) →
    Nonempty (Derivation body Γ (codePair mr dr wr)) →
    Nonempty (Derivation body Γ (programGraph maximum mid ![wl,wr])) →
    Nonempty (Derivation body Γ (programGraph maximum width ![k,mid])) →
    Nonempty (Derivation body Γ (programGraph numberedJoin p ![k,ml,mr])) →
    NumberedJoinBounds body Γ p k dl dr wl wr width

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets
