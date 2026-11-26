module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositive
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open NumberedWindowInternalParameterizedAddressPositive (addressAt wrapFoldAt)
open NumberedWindowInternalSparseAddressPositive

attribute [local irreducible] programGraph

private abbrev branchInput : Fin 5 → Program 3 := ![atAddress rawContext 0,atAddress rawResult 0,
  atAddress rawLeast 0,.projection 1,atAddress rawLeast 2]

abbrev call {α : Type} (xs : Fin 3 → OTerm α) (c t l r : OTerm α) : Fin 5 → OTerm α :=
  ![c,t,l,xs 1,r]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem actualArgs (xs : Fin 3 → OTerm α) (c t l r : OTerm α)
    (cx : Nonempty (Derivation body Γ (programGraph (atAddress rawContext 0) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult 0) t xs)))
    (src : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 0) l xs)))
    (dst : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 2) r xs))) :
    ∀ i, Nonempty (Derivation body Γ (programGraph (branchInput i) (call xs c t l r i) xs)) := by
  intro i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i
  · exact cx
  · exact ty
  · exact src
  · exact projectionValue (1 : Fin 3) xs
  · exact dst

theorem foldRead (P : Program 5) (xs : Fin 3 → OTerm α) (c t l r : OTerm α)
    (cx : Nonempty (Derivation body Γ (programGraph (atAddress rawContext 0) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult 0) t xs)))
    (src : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 0) l xs)))
    (dst : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 2) r xs)))
    (known : Nonempty (Derivation body Γ (programGraph (wrapFoldAt P) (suc z) xs))) :
    Nonempty (Derivation body Γ (programGraph P (suc z) (call xs c t l r))) :=
  compositionRecover P branchInput (suc z) xs (call xs c t l r) known
    (actualArgs xs c t l r cx ty src dst)

theorem foldIntro (P : Program 5) (xs : Fin 3 → OTerm α) (c t l r : OTerm α)
    (cx : Nonempty (Derivation body Γ (programGraph (atAddress rawContext 0) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult 0) t xs)))
    (src : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 0) l xs)))
    (dst : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 2) r xs)))
    (known : Nonempty (Derivation body Γ (programGraph P (suc z) (call xs c t l r)))) :
    Nonempty (Derivation body Γ (programGraph (wrapFoldAt P) (suc z) xs)) :=
  compositionValue P branchInput (suc z) xs (call xs c t l r) known
    (actualArgs xs c t l r cx ty src dst)

private abbrev testsType (P : Program 5) :=
  conjunction (sameField rawResult) (wrapFoldAt P)
private abbrev testsCtx (P : Program 5) :=
  conjunction (sameField rawContext) (testsType P)
private abbrev testsRight (cv tv : Program 1) (P : Program 5) :=
  conjunction (sideGood cv tv 2) (testsCtx P)

abbrev Seen (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p : Program 3) (xs : Fin 3 → OTerm α) : Prop :=
  Nonempty (Derivation body Γ (programGraph p (suc z) xs))

@[expose] def GateFacts (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (cv tv : Program 1) (P : Program 5) (xs : Fin 3 → OTerm α) : Prop :=
  Seen body Γ (sideGood cv tv 0) xs ∧
    (Seen body Γ (sideGood cv tv 2) xs ∧
      (Seen body Γ (sameField rawContext) xs ∧
        (Seen body Γ (sameField rawResult) xs ∧ Seen body Γ (wrapFoldAt P) xs)))

theorem gateRead (cv tv : Program 1) (P : Program 5) (xs : Fin 3 → OTerm α)
    (accepted : Seen body Γ (addressAt cv tv P) xs) :
    GateFacts body Γ cv tv P xs := by
  obtain ⟨left⟩ := conjunctionRecover (sideGood cv tv 0) (testsRight cv tv P) xs accepted
  obtain ⟨right⟩ := conjunctionRecover (sideGood cv tv 2) (testsCtx P) xs
    ⟨Derivation.conjunctionRight left⟩
  obtain ⟨context⟩ := conjunctionRecover (sameField rawContext) (testsType P) xs
    ⟨Derivation.conjunctionRight right⟩
  obtain ⟨ty⟩ := conjunctionRecover (sameField rawResult) (wrapFoldAt P) xs
    ⟨Derivation.conjunctionRight context⟩
  exact ⟨⟨Derivation.conjunctionLeft left⟩,⟨Derivation.conjunctionLeft right⟩,
    ⟨Derivation.conjunctionLeft context⟩,⟨Derivation.conjunctionLeft ty⟩,⟨Derivation.conjunctionRight ty⟩⟩

theorem gateIntro (cv tv : Program 1) (P : Program 5) (xs : Fin 3 → OTerm α)
    (known : GateFacts body Γ cv tv P xs) : Seen body Γ (addressAt cv tv P) xs := by
  obtain ⟨l,r,c,t,h⟩ := known
  have typ := conjunctionAccept (sameField rawResult) (wrapFoldAt P) xs t h
  have ctx := conjunctionAccept (sameField rawContext) (testsType P) xs c typ
  have seen := conjunctionAccept (sideGood cv tv 2) (testsCtx P) xs r ctx
  exact conjunctionAccept (sideGood cv tv 0) (testsRight cv tv P) xs l seen

#print axioms foldRead
#print axioms foldIntro
#print axioms gateRead
#print axioms gateIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof
