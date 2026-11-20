module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenFoldProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive

attribute [local irreducible] programGraph positive

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

theorem foldRead (raw : Program 5) (least : Program 3) (xs : Fin 3 → OTerm α) (c t l r : OTerm α)
    (cx : Nonempty (Derivation body Γ (programGraph (atAddress rawContext 0) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult 0) t xs)))
    (src : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 0) l xs)))
    (dst : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 2) r xs)))
    (known : Nonempty (Derivation body Γ (programGraph (callFold raw least) (suc z) xs))) :
    Nonempty (Derivation body Γ (programGraph (positive raw least) (suc z) (call xs c t l r))) :=
  compositionRecover (positive raw least) branchInput (suc z) xs (call xs c t l r) known
    (actualArgs xs c t l r cx ty src dst)

theorem foldIntro (raw : Program 5) (least : Program 3) (xs : Fin 3 → OTerm α) (c t l r : OTerm α)
    (cx : Nonempty (Derivation body Γ (programGraph (atAddress rawContext 0) c xs)))
    (ty : Nonempty (Derivation body Γ (programGraph (atAddress rawResult 0) t xs)))
    (src : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 0) l xs)))
    (dst : Nonempty (Derivation body Γ (programGraph (atAddress rawLeast 2) r xs)))
    (known : Nonempty (Derivation body Γ (programGraph (positive raw least) (suc z) (call xs c t l r)))) :
    Nonempty (Derivation body Γ (programGraph (callFold raw least) (suc z) xs)) :=
  compositionValue (positive raw least) branchInput (suc z) xs (call xs c t l r) known
    (actualArgs xs c t l r cx ty src dst)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenFoldProof
