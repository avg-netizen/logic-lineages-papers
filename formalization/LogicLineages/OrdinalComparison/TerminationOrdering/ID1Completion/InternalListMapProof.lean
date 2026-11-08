module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalListCodec InternalRawListRecursion InternalListMap SourceComputabilityFormulaSupportProof
open InternalRawListRecursionSyntaxProof InternalRawListRecursionProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem mapHeadValue {k : Nat} (transform : Program (k+1))
    (head result mappedHead : OTerm α) (params : Fin k → OTerm α)
    (hh : Nonempty (Derivation body Gamma (programGraph transform mappedHead (Fin.cons head params)))) :
    Nonempty (Derivation body Gamma
      (programGraph (mapHead transform) mappedHead (Fin.cons head (Fin.cons result params)))) := by
  apply compositionValue transform
    (Fin.cons (.projection 0) (fun i => .projection i.succ.succ)) mappedHead
    (Fin.cons head (Fin.cons result params)) (Fin.cons head params) hh
  intro i
  refine Fin.cases ?_ (fun q => ?_) i
  · exact projectionValue (0 : Fin (k+2)) (Fin.cons head (Fin.cons result params))
  · exact projectionValue q.succ.succ (Fin.cons head (Fin.cons result params))

theorem mapStepValue {k : Nat} (transform : Program (k+1))
    (head result mappedHead out : OTerm α) (params : Fin k → OTerm α)
    (hh : Nonempty (Derivation body Gamma (programGraph transform mappedHead (Fin.cons head params))))
    (hc : Nonempty (Derivation body Gamma
      (programGraph consCode out (Fin.cons mappedHead (Fin.cons result Fin.elim0))))) :
    Nonempty (Derivation body Gamma
      (programGraph (mapStep transform) out (Fin.cons head (Fin.cons result params)))) := by
  apply compositionValue consCode
    (Fin.cons (mapHead transform) (Fin.cons (.projection 1) Fin.elim0)) out
    (Fin.cons head (Fin.cons result params)) (Fin.cons mappedHead (Fin.cons result Fin.elim0)) hc
  intro i
  exact Fin.cases (mapHeadValue transform head result mappedHead params hh)
    (Fin.cases (projectionValue (1 : Fin (k+2)) (Fin.cons head (Fin.cons result params)))
      (fun q => Fin.elim0 q)) i

theorem consBackward {k : Nat} (transform : Program (k+1))
    (code head tail mappedHead mappedTail out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0)))))
    (hh : Nonempty (Derivation body Gamma
      (programGraph transform mappedHead (Fin.cons head params))))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (InternalListMap.map transform) mappedTail (Fin.cons tail params))))
    (ho : Nonempty (Derivation body Gamma
      (programGraph consCode out (Fin.cons mappedHead (Fin.cons mappedTail Fin.elim0))))) :
    Nonempty (Derivation body Gamma
      (programGraph (InternalListMap.map transform) out (Fin.cons code params))) := by
  obtain ⟨hs⟩ := mapStepValue transform head mappedTail mappedHead out params hh ho
  obtain ⟨ht⟩ := ht
  have hex : Nonempty (Derivation body Gamma (consStep zero (mapStep transform) out head tail params)) := by
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb mappedTail)
    rw [consStepInstance]
    exact Derivation.conjunctionIntroduction ht hs
  obtain ⟨heq⟩ := closedApply
    (actualOriginalListRecursionCons body k zero (mapStep transform) α code head tail out params) hc
  obtain ⟨hex⟩ := hex
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hex⟩

theorem consForward {k : Nat} (transform : Program (k+1))
    (code head tail mappedHead mappedTail out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0)))))
    (hh : Nonempty (Derivation body Gamma
      (programGraph transform mappedHead (Fin.cons head params))))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (InternalListMap.map transform) mappedTail (Fin.cons tail params))))
    (ho : Nonempty (Derivation body Gamma
      (programGraph (InternalListMap.map transform) out (Fin.cons code params)))) :
    Nonempty (Derivation body Gamma
      (programGraph consCode out (Fin.cons mappedHead (Fin.cons mappedTail Fin.elim0)))) := by
  apply programCases consCode (Fin.cons mappedHead (Fin.cons mappedTail Fin.elim0)) _
  intro β j Delta value hj hv
  simp only [programRename,consTermRename,emptyRename]
  simp only [consTermRename,emptyRename] at hv
  have hc' := renameInto hc j Delta hj
  have hh' := renameInto hh j Delta hj
  have ht' := renameInto ht j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hc' hh' ht' ho'
  have hmap := consBackward transform (code.relabel j) (head.relabel j) (tail.relabel j)
    (mappedHead.relabel j) (mappedTail.relabel j) value (fun i => (params i).relabel j) hc' hh' ht' hv
  exact outputTransport consCode value (out.relabel j)
    (Fin.cons (mappedHead.relabel j) (Fin.cons (mappedTail.relabel j) Fin.elim0))
    (valueUnique (InternalListMap.map transform) value (out.relabel j)
      (Fin.cons (code.relabel j) (fun i => (params i).relabel j)) hmap ho') hv

theorem actualOriginalListMapZero : InternalListMapTargets.ActualOriginalListMapZero := by
  intro body k transform α out params
  let P := programGraph (InternalListMap.map transform) out (Fin.cons z params)
  let Q := equal out z
  obtain ⟨heq⟩ := actualOriginalListRecursionZero body k zero (mapStep transform) α out params
  have hz (Gamma : List (Formula α)) :
      Nonempty (Derivation body Gamma (programGraph (zero : Program k) z params)) :=
    InternalAcceptanceConjunctionProof.constantZeroValue params
  have forward : Nonempty (Derivation body [P] Q) := by
    have hzero := closedApply ⟨Derivation.conjunctionLeft heq⟩
      (Nonempty.intro (Derivation.hypothesis (Gamma := [P]) List.mem_cons_self))
    change Nonempty (Derivation body [P] (equal out z))
    rw [equalEqn]
    exact valueUnique zero out z params hzero (hz [P])
  have backward : Nonempty (Derivation body [Q] P) := by
    have hq : Derivation body [Q] (eqn out z) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    have hzero := outputTransport zero z out params ⟨InternalTagArithmeticSupportProof.symm hq⟩ (hz [Q])
    exact closedApply ⟨Derivation.conjunctionRight heq⟩ hzero
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem actualOriginalListMapCons : InternalListMapTargets.ActualOriginalListMapCons := by
  intro body k transform α code head tail mappedHead mappedTail out params
  let A := programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0)) ⊓
    (programGraph transform mappedHead (Fin.cons head params) ⊓
      programGraph (InternalListMap.map transform) mappedTail (Fin.cons tail params))
  let P := programGraph (InternalListMap.map transform) out (Fin.cons code params)
  let Q := programGraph consCode out (Fin.cons mappedHead (Fin.cons mappedTail Fin.elim0))
  have forward : Nonempty (Derivation body [P,A] Q) :=
    consForward transform code head tail mappedHead mappedTail out params
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q,A] P) :=
    consBackward transform code head tail mappedHead mappedTail out params
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
