module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalParameterizedApplicationStepCheckerRepeatSupportProof OriginalNonapplicationCheckerFixedSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalListCodec InternalListCodecSupportProof InternalListInduction InternalListInductionProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (transition : Program 2) (code initial parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fixedRow transition code)))
    (hf : Nonempty (Derivation body Gamma (graph2 transition initial initial parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial code initial parameter)) := by
  have h := actualFiniteUniversalElimination body α 2 Gamma (fixedBody transition code)
    (fun i => emb (![initial,parameter] i)) hrow
  rw [fixedBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem zeroRow (transition : Program 2) :
    Nonempty (Derivation body Gamma (fixedRow transition z)) := by
  unfold fixedRow
  apply actualFiniteUniversalIntroduction body α 2 Gamma
  let initial : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let A := graph2 transition initial initial parameter
  obtain ⟨d⟩ := repeatZeroValue (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) transition initial parameter
  simpa only [fixedBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem consCore (transition : Program 2) (code head tail initial parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fixedRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hf : Nonempty (Derivation body Gamma (graph2 transition initial initial parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial code initial parameter)) :=
  repeatConsValue transition code head tail initial initial initial parameter hc
    (rowApply transition tail initial parameter hrow hf) hf

theorem consRow (transition : Program 2) (code head tail : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fixedRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail))) :
    Nonempty (Derivation body Gamma (fixedRow transition code)) := by
  unfold fixedRow
  apply actualFiniteUniversalIntroduction body α 2 Gamma
  let initial : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let c := code.relabel (Sum.inl : α → α ⊕ Fin 2)
  let h := head.relabel (Sum.inl : α → α ⊕ Fin 2)
  let t := tail.relabel (Sum.inl : α → α ⊕ Fin 2)
  let A := graph2 transition initial initial parameter
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 2))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [fixedRowRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  obtain ⟨d⟩ := consCore transition c h t initial parameter hrow' hc'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Instantiate the paid full-language list-code induction, not native Nat
induction or a fresh numerical recursion on a decoded certificate. -/
theorem allRows (transition : Program 2) (code : OTerm α) :
    Nonempty (Derivation body Gamma (fixedRow transition code)) := by
  let theta : Formula (α ⊕ Fin 1) := fixedRow transition (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [fixedAtCode]
    exact zeroRow transition
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body α 3 Gamma
    simp only [constructorBody,theta,fixedAtIndex]
    let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph c h t
    let R := fixedRow transition t
    obtain ⟨d⟩ := consRow (body := body)
      (Gamma := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)) transition c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := actualOriginalListInductionAtCode body α Gamma theta code
    ⟨Derivation.conjunctionIntroduction hz hs⟩
  rw [fixedAtCode] at h
  exact h

theorem fixedValue (transition : Program 2) (code initial parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph2 transition initial initial parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial code initial parameter)) :=
  rowApply transition code initial parameter (allRows transition code) hf

theorem fixedRecover (transition : Program 2) (out code initial parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph2 transition initial initial parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition out code initial parameter))) :
    Nonempty (Derivation body Gamma (eqn out initial)) :=
  valueUnique (repeatP transition) out initial
    (Fin.cons code (Fin.cons initial (Fin.cons parameter Fin.elim0))) hr
    (fixedValue transition code initial parameter hf)

theorem actualOriginalParameterizedRawListFixedPoint :
    OriginalNonapplicationCheckerTargets.ActualOriginalParameterizedRawListFixedPoint := by
  intro transition body α Delta out code initial parameter
  let A := graph2 transition initial initial parameter
  let R := repeatGraph transition out code initial parameter
  let E := equal out initial
  have forward : Nonempty (Derivation body (A :: Delta) (R.imp E)) := by
    obtain ⟨d⟩ := fixedRecover (body := body) (Gamma := R :: A :: Delta)
      transition out code initial parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (by simpa only [E,equalEqn] using d)⟩
  have backward : Nonempty (Derivation body (A :: Delta) (E.imp R)) := by
    have he : Derivation body (E :: A :: Delta) (eqn out initial) := by
      simpa only [E,equalEqn] using
        (Derivation.hypothesis List.mem_cons_self : Derivation body (E :: A :: Delta) E)
    obtain ⟨d⟩ := outputTransport (repeatP transition) initial out
      (Fin.cons code (Fin.cons initial (Fin.cons parameter Fin.elim0))) ⟨symm he⟩
      (fixedValue transition code initial parameter
        (show Nonempty (Derivation body (E :: A :: Delta) A) from
          ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩))
    exact ⟨Derivation.implicationIntroduction d⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction forward backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedProof
