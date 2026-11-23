module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSelectOwnerEmissionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedCode numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (nodeReport)
open NumberedWindowInternalAtomicApplicationShape (auxAddressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (auxGraph)

/-- The actual literal constructors, composed on the held eight
Select fields [context,domain,residual,function,head,label,base,extras].
The input label is already the original selected predecessor. -/
def ownerField : Program 8 :=
  .composition numberedCode ![.projection 7,.projection 4,.projection 1,.projection 5,.projection 6]

def selectOwnerApplication : Program 8 :=
  .composition auxAddressEmitter ![.projection 0,.projection 1,.projection 2,.projection 3,ownerField]

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenSelectOwnerField (c dom result fn head lower base extras : OTerm α) :
    Nonempty (Derivation B Γ (programGraph ownerField (numberedTerm head dom lower base extras)
      ![c,dom,result,fn,head,lower,base,extras])) := by
  let xs : Fin 8 → OTerm α := ![c,dom,result,fn,head,lower,base,extras]
  unfold ownerField
  apply compositionValue numberedCode _ (numberedTerm head dom lower base extras) xs
    ![extras,head,dom,lower,base] (nodeReport head dom lower base extras)
  intro j
  exact Fin.cases (projectionValue 7 xs)
    (Fin.cases (projectionValue 4 xs)
      (Fin.cases (projectionValue 1 xs)
        (Fin.cases (projectionValue 5 xs) (Fin.cases (projectionValue 6 xs)
          (fun k => Fin.elim0 k))))) j

theorem exact_OpenSelectOwnerApplication (c dom result fn head lower base extras : OTerm α) :
    Nonempty (Derivation B Γ (programGraph selectOwnerApplication
      (auxAddressTerm c dom result fn (numberedTerm head dom lower base extras))
      ![c,dom,result,fn,head,lower,base,extras])) := by
  let xs : Fin 8 → OTerm α := ![c,dom,result,fn,head,lower,base,extras]
  let owner := numberedTerm head dom lower base extras
  unfold selectOwnerApplication
  apply compositionValue auxAddressEmitter _ (auxAddressTerm c dom result fn owner) xs
    ![c,dom,result,fn,owner] (auxGraph c dom result fn owner)
  intro j
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs)
        (Fin.cases (projectionValue 3 xs)
          (Fin.cases (exact_OpenSelectOwnerField c dom result fn head lower base extras)
            (fun k => Fin.elim0 k))))) j

#print axioms exact_OpenSelectOwnerField
#print axioms exact_OpenSelectOwnerApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalSelectOwnerEmissionProof
