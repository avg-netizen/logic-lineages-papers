module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSelectOwnerEmissionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedJLexBlockProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSelectOwnerFiniteUseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open NumberedWindowInternalConstructorLabelStratumTargets (FiniteMatrix finiteLabels finiteLabelBody)
open NumberedWindowInternalLiteralPackedJLexBlockTargets (specialize currentAt useLater)
open NumberedWindowInternalLiteralPackedJLexBlockProof (specializeClosedBlock)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSelectOwnerEmissionProof
  (ownerField selectOwnerApplication exact_OpenSelectOwnerApplication)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Consume the real finite-label universal at the selected predecessor
and at [context,extras,domain,owner-address]. The matrix's own typing
premises remain in its instance; this is not a reduction certificate. -/
theorem exact_OpenSelectOwnerFiniteUse (finite : FiniteMatrix α)
    (c dom result fn head lower base extras : OTerm α)
    (paid : Nonempty (Derivation B Γ (finiteLabels finite))) :
    let key := addressTerm c dom (numberedTerm head dom lower base extras)
    let inst := useLater finite (currentAt lower) ![c,extras,dom,key]
    let emitted := programGraph selectOwnerApplication
      (auxAddressTerm c dom result fn (numberedTerm head dom lower base extras))
      ![c,dom,result,fn,head,lower,base,extras]
    Nonempty (Derivation B Γ (emitted ⊓ inst)) := by
  intro key inst emitted
  obtain ⟨all⟩ := paid
  have use := Derivation.universalElimination (emb lower) all
  change Derivation B Γ ((allBlock finite).subst (currentAt lower)) at use
  rw [specializeClosedBlock] at use
  obtain ⟨found⟩ := actualFiniteUniversalElimination B α 4 Γ
    (specialize finite (currentAt lower)) (fun j => emb ((![c,extras,dom,key] : Fin 4 → OTerm α) j))
    ⟨use⟩
  obtain ⟨packed⟩ := exact_OpenSelectOwnerApplication (B := B) (Γ := Γ) c dom result fn head lower base extras
  exact ⟨Derivation.conjunctionIntroduction packed found⟩

#print axioms exact_OpenSelectOwnerFiniteUse
end LogicLineages.PersistentMarking.NumberedWindowInternalSelectOwnerFiniteUseProof
