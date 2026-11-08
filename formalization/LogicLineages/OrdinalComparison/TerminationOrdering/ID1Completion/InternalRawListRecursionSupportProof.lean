module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphSuccessorIntroductionProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem constantZero {k : Nat} (params : Fin k → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (zero : Program k) z params)) := by
  apply compositionValue .zero (Fin.elim0 : Fin 0 → Program k) z params Fin.elim0 (zeroValue Fin.elim0)
  intro i
  exact Fin.elim0 i

theorem recursionNext {k : Nat} (base : Program k) (step : Program (k + 2))
    (out old index : OTerm α) (params : Fin k → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph (.recursion base step) old (Fin.cons index params))))
    (hs : Nonempty (Derivation body Gamma (programGraph step out (Fin.cons index (Fin.cons old params))))) :
    Nonempty (Derivation body Gamma (programGraph (.recursion base step) out (Fin.cons (suc index) params))) :=
  recursionSuccessorIntroduction Gamma _ _ out index old params hp hs

/-- Recover the step at an already supplied predecessor value using original
totality, introduction and functionality. -/
theorem recursionRecover {k : Nat} (base : Program k) (step : Program (k + 2))
    (out old index : OTerm α) (params : Fin k → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph (.recursion base step) old (Fin.cons index params))))
    (hs : Nonempty (Derivation body Gamma (programGraph (.recursion base step) out (Fin.cons (suc index) params)))) :
    Nonempty (Derivation body Gamma (programGraph step out (Fin.cons index (Fin.cons old params)))) := by
  apply programCases step (Fin.cons index (Fin.cons old params)) _
  intro β j Delta v hj hv
  simp only [programRename,consTermRename]
  have hp' := renameInto hp j Delta hj
  have hs' := renameInto hs j Delta hj
  simp only [programRename,consTermRename,sucRelabel] at hp' hs' hv
  have he := recursionNext base step v (old.relabel j) (index.relabel j)
    (fun i => (params i).relabel j) hp' hv
  obtain ⟨eq⟩ := valueUnique (.recursion base step) v (out.relabel j)
    (Fin.cons (suc (index.relabel j)) (fun i => (params i).relabel j)) he hs'
  exact outputTransport step v (out.relabel j)
    (Fin.cons (index.relabel j) (Fin.cons (old.relabel j) (fun i => (params i).relabel j))) ⟨eq⟩ hv

theorem consHead (code head tail : OTerm α)
    (h : Nonempty (Derivation body Gamma (consGraph code head tail))) :
    Nonempty (Derivation body Gamma (unaryGraph headCode head code)) := by
  obtain ⟨d⟩ := consDestruction code head tail h
  exact ⟨Derivation.conjunctionLeft d⟩

theorem consTail (code head tail : OTerm α)
    (h : Nonempty (Derivation body Gamma (consGraph code head tail))) :
    Nonempty (Derivation body Gamma (unaryGraph tailCode tail code)) := by
  obtain ⟨d⟩ := consDestruction code head tail h
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩

theorem tableBaseValue {k : Nat} (base : Program k) (value out : OTerm α)
    (params : Fin k → OTerm α)
    (hv : Nonempty (Derivation body Gamma (programGraph base value params)))
    (hc : Nonempty (Derivation body Gamma (consGraph out value z))) :
    Nonempty (Derivation body Gamma (programGraph (tableBase base) out params)) := by
  apply compositionValue consCode (Fin.cons base (Fin.cons zero Fin.elim0)) out params
    (Fin.cons value (Fin.cons z Fin.elim0)) hc
  intro i
  exact Fin.cases hv (Fin.cases (constantZero params) (fun j => Fin.elim0 j)) i

theorem tableZeroValue {k : Nat} (base : Program k) (step : Program (k + 2))
    (value out : OTerm α) (params : Fin k → OTerm α)
    (hv : Nonempty (Derivation body Gamma (programGraph base value params)))
    (hc : Nonempty (Derivation body Gamma (consGraph out value z))) :
    Nonempty (Derivation body Gamma (tableGraph base step out z params)) :=
  recursionZeroValue (tableBase base) (tableStep step) out params (tableBaseValue base value out params hv hc)

theorem tableStepValue {k : Nat} (step : Program (k + 2)) (value out index previous : OTerm α)
    (params : Fin k → OTerm α)
    (hv : Nonempty (Derivation body Gamma (programGraph (nextValue step) value
      (Fin.cons index (Fin.cons previous params)))))
    (hc : Nonempty (Derivation body Gamma (consGraph out value previous))) :
    Nonempty (Derivation body Gamma (programGraph (tableStep step) out
      (Fin.cons index (Fin.cons previous params)))) := by
  apply compositionValue consCode (Fin.cons (nextValue step) (Fin.cons (.projection 1) Fin.elim0))
    out (Fin.cons index (Fin.cons previous params)) (Fin.cons value (Fin.cons previous Fin.elim0)) hc
  intro i
  exact Fin.cases hv
    (Fin.cases (projectionValue 1 (Fin.cons index (Fin.cons previous params))) (fun j => Fin.elim0 j)) i

theorem tableNext {k : Nat} (base : Program k) (step : Program (k + 2))
    (value out index previous : OTerm α) (params : Fin k → OTerm α)
    (hp : Nonempty (Derivation body Gamma (tableGraph base step previous index params)))
    (hv : Nonempty (Derivation body Gamma (programGraph (nextValue step) value
      (Fin.cons index (Fin.cons previous params)))))
    (hc : Nonempty (Derivation body Gamma (consGraph out value previous))) :
    Nonempty (Derivation body Gamma (tableGraph base step out (suc index) params)) :=
  recursionNext (tableBase base) (tableStep step) out previous index params hp
    (tableStepValue step value out index previous params hv hc)

theorem tableTail {k : Nat} (base : Program k) (step : Program (k + 2))
    (old out index : OTerm α) (params : Fin k → OTerm α)
    (hp : Nonempty (Derivation body Gamma (tableGraph base step old index params)))
    (hs : Nonempty (Derivation body Gamma (tableGraph base step out (suc index) params))) :
    Nonempty (Derivation body Gamma (unaryGraph tailCode old out)) := by
  have ht := recursionRecover (tableBase base) (tableStep step) out old index params hp hs
  apply programCases (nextValue step) (Fin.cons index (Fin.cons old params)) _
  intro β j Delta v hj hv
  simp only [unaryGraphRename]
  have ht' := renameInto ht j Delta hj
  simp only [programRename,consTermRename] at ht' hv
  have hc : Nonempty (Derivation body Delta
      (consGraph (out.relabel j) v (old.relabel j))) := by
    apply compositionRecover consCode
      (Fin.cons (nextValue step) (Fin.cons (.projection 1) Fin.elim0))
      (out.relabel j) (Fin.cons (index.relabel j) (Fin.cons (old.relabel j) (fun i => (params i).relabel j)))
      (Fin.cons v (Fin.cons (old.relabel j) Fin.elim0)) ht'
    intro i
    exact Fin.cases hv
      (Fin.cases (projectionValue (1 : Fin (k + 2))
        (Fin.cons (index.relabel j) (Fin.cons (old.relabel j) (fun a => (params a).relabel j))))
        (fun e => Fin.elim0 e)) i
  exact consTail (out.relabel j) v (old.relabel j) hc

theorem recValue {k : Nat} (base : Program k) (step : Program (k + 2))
    (out code tab : OTerm α) (params : Fin k → OTerm α)
    (ht : Nonempty (Derivation body Gamma (tableGraph base step tab code params)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode out tab))) :
    Nonempty (Derivation body Gamma (recGraph base step out code params)) := by
  apply compositionValue headCode (fun _ : Fin 1 => table base step) out (Fin.cons code params)
    (Fin.cons tab Fin.elim0) hh
  intro i
  obtain rfl := Fin.eq_zero i
  exact ht

theorem recHead {k : Nat} (base : Program k) (step : Program (k + 2))
    (out code tab : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (recGraph base step out code params)))
    (ht : Nonempty (Derivation body Gamma (tableGraph base step tab code params))) :
    Nonempty (Derivation body Gamma (unaryGraph headCode out tab)) := by
  apply compositionRecover headCode (fun _ : Fin 1 => table base step) out (Fin.cons code params)
    (Fin.cons tab Fin.elim0) hr
  intro i
  obtain rfl := Fin.eq_zero i
  exact ht

theorem dropZero (code : OTerm α) :
    Nonempty (Derivation body Gamma (dropGraph code z code)) :=
  recursionZeroValue (.projection (0 : Fin 1))
    (.composition tailCode (fun _ : Fin 1 => .projection (1 : Fin 3)))
    code (Fin.cons code Fin.elim0) (projectionValue (0 : Fin 1) (Fin.cons code Fin.elim0))

theorem dropNext (out old index code : OTerm α)
    (hp : Nonempty (Derivation body Gamma (dropGraph old index code)))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode out old))) :
    Nonempty (Derivation body Gamma (dropGraph out (suc index) code)) := by
  apply recursionNext (.projection (0 : Fin 1))
    (.composition tailCode (fun _ : Fin 1 => .projection (1 : Fin 3)))
    out old index (Fin.cons code Fin.elim0) hp
  apply compositionValue tailCode (fun _ : Fin 1 => .projection (1 : Fin 3)) out
    (Fin.cons index (Fin.cons old (Fin.cons code Fin.elim0))) (Fin.cons old Fin.elim0) ht
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 3) (Fin.cons index (Fin.cons old (Fin.cons code Fin.elim0)))

theorem lookupValue (out index code rest : OTerm α)
    (hd : Nonempty (Derivation body Gamma (dropGraph rest index code)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode out rest))) :
    Nonempty (Derivation body Gamma (lookupGraph out index code)) := by
  apply compositionValue headCode (fun _ : Fin 1 => drop) out
    (Fin.cons index (Fin.cons code Fin.elim0)) (Fin.cons rest Fin.elim0) hh
  intro i
  obtain rfl := Fin.eq_zero i
  exact hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
