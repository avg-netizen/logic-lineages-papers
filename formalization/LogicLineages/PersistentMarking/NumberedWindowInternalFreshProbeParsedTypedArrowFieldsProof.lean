module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (equalEqn outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePairChecks (exact_FieldConsValue exact_OpenFieldConsInjective)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem literalArrow (σ τ : ProbeTy) :
    Nonempty (Derivation body Γ (programGraph fieldCons (numeral (typeCode (.arrow σ τ)))
      ![numeral (typeCode σ),numeral (typeCode τ)])) := by
  let xs := typeCode σ ::ᵥ typeCode τ ::ᵥ nil
  have val : evaluate fieldCons xs = typeCode (.arrow σ τ) :=
    exact_FieldConsValue (typeCode σ) (typeCode τ)
  obtain ⟨d⟩ := NumberedWindowNumeralGraphChecks.exact_NumeralGraph 2 fieldCons xs body α Γ
  have h : (NumberedWindowNumeralGraphTargets.inputs xs : Fin 2 → OTerm α) =
      ![numeral (typeCode σ),numeral (typeCode τ)] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [val,h] at d
  exact ⟨d⟩

/-- Compare two actual sparse-cell graphs at the same result. Numerical
calibration was used only for the two closed literal component codes. -/
theorem actualArrowFields (σ τ : ProbeTy) (r d e : OTerm α)
    (hr : Nonempty (Derivation body Γ (equal r (numeral (typeCode (.arrow σ τ))))))
    (hshape : Nonempty (Derivation body Γ (equal r (consTerm d e)))) :
    Nonempty (Derivation body Γ
      (equal d (numeral (typeCode σ)) ⊓ equal e (numeral (typeCode τ)))) := by
  rw [equalEqn] at hr hshape
  obtain ⟨er⟩ := hr
  obtain ⟨es⟩ := hshape
  obtain ⟨left⟩ := outputTransport fieldCons (consTerm d e) r ![d,e] ⟨symm es⟩ (consGraph d e)
  obtain ⟨right⟩ := outputTransport fieldCons (numeral (typeCode (.arrow σ τ))) r
    ![numeral (typeCode σ),numeral (typeCode τ)] ⟨symm er⟩ (literalArrow σ τ)
  obtain ⟨rule⟩ := exact_OpenFieldConsInjective body α r d e (numeral (typeCode σ)) (numeral (typeCode τ))
  exact ⟨Derivation.implicationElimination (weakenClosed rule Γ)
    (Derivation.conjunctionIntroduction left right)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof
