module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalPathChecker InternalApplicationPathLift InternalApplicationPathLiftSyntaxProof
open InternalApplicationCertificateConstructors InternalPathCheckerProof
open InternalListCodec InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalSourceInversionSupportProof InternalBetaTotalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem vertexInputTransport (vertex : Program 5) (ps : Parameters α) (out x y : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn x y)))
    (h : Nonempty (Derivation body Gamma (vertexAt vertex ps out x))) :
    Nonempty (Derivation body Gamma (vertexAt vertex ps out y)) := by
  apply graphInputTransport body α 5 Gamma (OrdinaryArithmetic.graphFormula vertex)
    out (vertexInputs ps x) (vertexInputs ps y) _ h
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl (ps 0)⟩ (Fin.cases ⟨refl (ps 1)⟩
    (Fin.cases ⟨refl (ps 2)⟩ (Fin.cases ⟨refl (ps 3)⟩
      (Fin.cases he (fun q => Fin.elim0 q))))) i

theorem checkerCodeTransport (edge : Program 3) (positive : Bool)
    (x y code other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn code other)))
    (h : Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) x y code))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) x y other)) := by
  apply graphInputTransport body α 3 Gamma (OrdinaryArithmetic.graphFormula (checker edge positive))
    (suc z) (triple x y code) (triple x y other) _ h
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl x⟩ (Fin.cases ⟨refl y⟩ (Fin.cases he (fun q => Fin.elim0 q))) i

/-- Ordinary nil acceptance identifies both endpoints. Equal vertex inputs
have equal actual outputs, and the original mapper sends nil to nil. -/
theorem nilLift (edge : Program 3) (vertex invariant : Program 5) (ps : Parameters α)
    (x y out other mapped : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant false ps x y z out other mapped))) :
    Nonempty (Derivation body Gamma (pathGraph edge out other mapped)) := by
  obtain ⟨h⟩ := h
  have hp := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight h))
  have hv := Nonempty.intro (Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight h)))
  have hw := Nonempty.intro (Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))
  have hm := Nonempty.intro (Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))
  obtain ⟨he⟩ := nilRecover edge x y hp
  rw [equalEqn] at he
  have hv' := vertexInputTransport vertex ps out x y ⟨he⟩ hv
  have ho := valueUnique vertex out other (vertexInputs ps y) hv' hw
  have ho' : Nonempty (Derivation body Gamma (equal out other)) := by
    rw [equalEqn]
    exact ho
  have hz := nilAccept edge out other ho'
  obtain ⟨hmap⟩ := InternalApplicationPathMapProof.actualOriginalPathMapZero body vertex α mapped
    (ps 0) (ps 1) (ps 2) (ps 3)
  change Derivation body []
    ((mappedAt vertex (InternalApplicationPathMap.parameters (ps 0) (ps 1) (ps 2) (ps 3)) mapped z).iff
      (equal mapped z)) at hmap
  rw [parametersExpand] at hmap
  obtain ⟨hmz⟩ := closedApply ⟨Derivation.conjunctionLeft hmap⟩ hm
  rw [equalEqn] at hmz
  exact checkerCodeTransport edge false out other z mapped ⟨symm hmz⟩ hz

theorem positiveNonzero (edge : Program 3) (x y code : OTerm α)
    (h : Nonempty (Derivation body Gamma (positiveGraph edge x y code))) :
    Nonempty (Derivation body Gamma (eqn code z).not) := by
  obtain ⟨h⟩ := h
  let P := eqn code z
  obtain ⟨hz⟩ := checkerCodeTransport (body := body) (Gamma := P :: Gamma)
    edge true x y code z ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp h P⟩
  obtain ⟨hn⟩ := positiveNil (body := body) (Gamma := P :: Gamma) edge x y
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hz)⟩

/-- Positive acceptance excludes zero internally. Original head and tail
totality then provide actual constructor witnesses for every positive code. -/
theorem positiveConsCases (edge : Program 3) (x y code : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (positiveGraph edge x y code)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (raw tail : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 consCode (code.relabel j) raw tail)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hn := positiveNonzero edge x y code h
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSupportProof
