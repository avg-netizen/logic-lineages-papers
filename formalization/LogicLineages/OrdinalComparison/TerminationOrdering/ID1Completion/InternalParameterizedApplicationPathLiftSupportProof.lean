module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedPathChecker InternalParameterizedApplicationPathLift InternalParameterizedApplicationPathLiftSyntaxProof
open InternalApplicationCertificateConstructors InternalParameterizedPathCheckerProof
open InternalApplicationPathLiftSupportProof (vertexInputTransport)
open InternalApplicationPathLiftSyntaxProof (parametersExpand)
open InternalListCodec InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalSourceInversionSupportProof InternalBetaTotalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem checkerCodeTransport (edge : Program 4) (positive : Bool)
    (x y code other parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn code other)))
    (h : Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) x y code parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) x y other parameter)) := by
  apply graphInputTransport body α 4 Gamma (OrdinaryArithmetic.graphFormula (checker edge positive))
    (suc z) (quadruple x y code parameter) (quadruple x y other parameter) _ h
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl x⟩ (Fin.cases ⟨refl y⟩
    (Fin.cases he (Fin.cases ⟨refl parameter⟩ (fun q => Fin.elim0 q)))) i

/-- Ordinary nil acceptance identifies both endpoints. Equal vertex inputs
have equal actual outputs, and the original mapper sends nil to nil. -/
theorem nilLift (edge : Program 4) (vertex invariant : Program 5) (ps : Parameters α)
    (x y out other mapped : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant false ps x y z out other mapped))) :
    Nonempty (Derivation body Gamma (pathGraph edge out other mapped (ps 0))) := by
  obtain ⟨h⟩ := h
  have hp := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight h))
  have hv := Nonempty.intro (Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight h)))
  have hw := Nonempty.intro (Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))
  have hm := Nonempty.intro (Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))
  obtain ⟨he⟩ := nilRecover edge x y (ps 0) hp
  rw [equalEqn] at he
  have hv' := vertexInputTransport vertex ps out x y ⟨he⟩ hv
  have ho := valueUnique vertex out other (vertexInputs ps y) hv' hw
  have ho' : Nonempty (Derivation body Gamma (equal out other)) := by
    rw [equalEqn]
    exact ho
  have hz := nilAccept edge out other (ps 0) ho'
  obtain ⟨hmap⟩ := InternalApplicationPathMapProof.actualOriginalPathMapZero body vertex α mapped
    (ps 0) (ps 1) (ps 2) (ps 3)
  change Derivation body []
    ((mappedAt vertex (InternalApplicationPathMap.parameters (ps 0) (ps 1) (ps 2) (ps 3)) mapped z).iff
      (equal mapped z)) at hmap
  rw [parametersExpand] at hmap
  obtain ⟨hmz⟩ := closedApply ⟨Derivation.conjunctionLeft hmap⟩ hm
  rw [equalEqn] at hmz
  exact checkerCodeTransport edge false out other z mapped (ps 0) ⟨symm hmz⟩ hz

theorem positiveNonzero (edge : Program 4) (x y code parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (positiveGraph edge x y code parameter))) :
    Nonempty (Derivation body Gamma (eqn code z).not) := by
  obtain ⟨h⟩ := h
  let P := eqn code z
  obtain ⟨hz⟩ := checkerCodeTransport (body := body) (Gamma := P :: Gamma)
    edge true x y code z parameter ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp h P⟩
  obtain ⟨hn⟩ := positiveNil (body := body) (Gamma := P :: Gamma) edge x y parameter
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hz)⟩

/-- Positive acceptance excludes zero internally. Original head and tail
totality then provide actual constructor witnesses for every positive code. -/
theorem positiveConsCases (edge : Program 4) (x y code parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (positiveGraph edge x y code parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (raw tail : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 consCode (code.relabel j) raw tail)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hn := positiveNonzero edge x y code parameter h
  apply programCases headCode (Fin.cons code Fin.elim0) _
  intro β j Delta raw hj hh
  simp only [consTermRename,emptyRename] at hh
  have hn' := renameInto hn j Delta hj
  rw [nonzeroRename] at hn'
  apply programCases tailCode (Fin.cons (code.relabel j) Fin.elim0) _
  intro γ k Theta tail hk ht
  simp only [consTermRename,emptyRename] at ht
  have hn'' := renameInto hn' k Theta hk
  rw [nonzeroRename] at hn''
  have hh' := renameInto hh k Theta hk
  rw [unaryGraphRename] at hh'
  have hc := reconstructNonzero ((code.relabel j).relabel k) (raw.relabel k) tail hn'' hh' ht
  simp only [Term.relabel_relabel] at hc
  rw [formulaRelabelComposition]
  apply next γ (k ∘ j) Theta (raw.relabel k) tail _ hc
  intro p hp
  have hp' := hk (p.relabel j) (hj p hp)
  simpa only [formulaRelabelComposition] using hp'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSupportProof
