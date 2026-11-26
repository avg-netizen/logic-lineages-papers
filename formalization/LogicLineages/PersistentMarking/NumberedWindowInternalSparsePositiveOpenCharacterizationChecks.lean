module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationForwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveOpenCharacterizationTargets
open NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
open NumberedWindowInternalSparsePositiveOpenCharacterizationTerminalRulesProof (acceptAtState)
open NumberedWindowInternalSparsePositiveOpenCharacterizationForwardProof (forward)

private theorem backward {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (known : Nonempty (Derivation body Γ (certificateResult raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (acceptance raw least ctx ty source cert target)) := by
  obtain ⟨known⟩ := known
  have nz : Nonempty (Derivation body Γ (eqn cert z).not) := ⟨Derivation.conjunctionLeft known⟩
  have done : Nonempty (Derivation body Γ (successfulTerminal raw least ctx ty source cert target)) :=
    ⟨Derivation.conjunctionRight known⟩
  apply targetCases raw least ctx ty source cert target (acceptance raw least ctx ty source cert target) done
  intro β j Δ state hJ loop pair
  rw [acceptanceRename]
  have nn := renameInto nz j Δ hJ
  change Nonempty (Derivation body Δ (((eqn cert z).relabel j).not)) at nn
  rw [eqnRelabel,zRelabel] at nn
  exact acceptAtState raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (cert.relabel j) (target.relabel j) state nn loop pair

theorem exact_OpenPositiveCharacterization : OpenPositiveCharacterization := by
  intro body raw least α ctx ty source cert target
  simp only [equalEqn]
  let a := acceptance raw least ctx ty source cert target
  let b := certificateResult raw least ctx ty source cert target
  obtain ⟨f⟩ := forward (body := body) (Γ := [a]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := backward (body := body) (Γ := [b]) raw least ctx ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

#print axioms exact_OpenPositiveCharacterization
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationChecks
