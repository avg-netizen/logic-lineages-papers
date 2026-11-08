module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalPathChecker InternalApplicationPathLift InternalApplicationPathLiftSyntaxProof
open InternalApplicationPathLiftSupportProof InternalApplicationPathLiftCoreProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalClosedProgramsBindingProof InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The nil row is uniform in both endpoints and every actual map output. -/
theorem nilRow (edge : Program 3) (vertex invariant : Program 5) (ps : Parameters α) :
    Nonempty (Derivation body Gamma (row edge vertex invariant ps z)) := by
  apply actualFiniteUniversalIntroduction body α 5 Gamma (matrix edge vertex invariant ps z)
  unfold matrix
  rw [InternalTagArithmeticSyntaxProof.zRelabel]
  let ps' : Parameters (α ⊕ Fin 5) := fun i => (ps i).relabel Sum.inl
  let P := inputs edge vertex invariant false ps'
    (.var (.inr 0)) (.var (.inr 1)) z (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
  change Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
    (P.imp (pathGraph edge (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))))
  obtain ⟨h⟩ := nilLift (body := body) (Gamma := P :: Gamma.map (fun p => p.relabel Sum.inl))
    edge vertex invariant ps' (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Lift an arbitrary cons row under its literal constructor graph and the
tail row. The five bound terms are fresh in the original context. -/
theorem consRow (edge : Program 3) (vertex invariant : Program 5)
    (hInvariant : InvariantPreservation body edge invariant)
    (hEdge : EdgeCompatibility body edge vertex invariant)
    (ps : Parameters α) (code raw tail : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode code raw tail)))
    (hr : Nonempty (Derivation body Gamma (row edge vertex invariant ps tail))) :
    Nonempty (Derivation body Gamma (row edge vertex invariant ps code)) := by
  apply actualFiniteUniversalIntroduction body α 5 Gamma (matrix edge vertex invariant ps code)
  let ps' : Parameters (α ⊕ Fin 5) := fun i => (ps i).relabel Sum.inl
  let P := inputs edge vertex invariant false ps'
    (.var (.inr 0)) (.var (.inr 1)) (code.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
  let Delta := P :: Gamma.map (fun p => p.relabel Sum.inl)
  have hj : ∀ p ∈ Gamma, p.relabel (Sum.inl : α → α ⊕ Fin 5) ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hr' := renameInto hr Sum.inl Delta hj
  rw [rowRename] at hr'
  have hc' := renameInto hc Sum.inl Delta hj
  rw [graph2Rename] at hc'
  change Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
    (P.imp (pathGraph edge (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))))
  obtain ⟨h⟩ := consLift edge vertex invariant hInvariant hEdge false ps'
    (.var (.inr 0)) (.var (.inr 1)) (code.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (raw.relabel Sum.inl) (tail.relabel Sum.inl)
    hr' hc' (show Nonempty (Derivation body Delta P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Original list-code induction proves the invariant at every symbolic code.
There is no metatheoretic induction over a decoded standard-natural list. -/
theorem allRows (edge : Program 3) (vertex invariant : Program 5)
    (hInvariant : InvariantPreservation body edge invariant)
    (hEdge : EdgeCompatibility body edge vertex invariant)
    (ps : Parameters α) (code : OTerm α) :
    Nonempty (Derivation body Gamma (row edge vertex invariant ps code)) := by
  let theta : Formula (α ⊕ Fin 1) :=
    row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr 0))
  have hbase : Nonempty (Derivation body Gamma (InternalListInduction.atCode theta z)) := by
    dsimp only [theta]
    rw [rowAtCode]
    exact nilRow edge vertex invariant ps
  have hstep : Nonempty (Derivation body Gamma (InternalListInduction.constructors theta)) := by
    apply actualFiniteUniversalIntroduction body α 3 Gamma (InternalListInduction.constructorBody theta)
    change Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      ((graph2 InternalListCodec.consCode (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
        ((InternalListInduction.atIndex theta 2).imp (InternalListInduction.atIndex theta 0))))
    dsimp only [theta]
    rw [rowAtIndex,rowAtIndex]
    let ps' : Parameters (α ⊕ Fin 3) := fun i => (ps i).relabel Sum.inl
    let C := graph2 InternalListCodec.consCode
      (.var (.inr 0) : OTerm (α ⊕ Fin 3)) (.var (.inr 1)) (.var (.inr 2))
    let R := row edge vertex invariant ps' (.var (.inr 2))
    let Delta := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)
    have hc : Nonempty (Derivation body Delta C) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hr : Nonempty (Derivation body Delta R) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := consRow edge vertex invariant hInvariant hEdge ps'
      (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) hc hr
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
  obtain ⟨hbase⟩ := hbase
  obtain ⟨hstep⟩ := hstep
  have hp : Nonempty (Derivation body Gamma (InternalListInduction.premises theta)) :=
    ⟨Derivation.conjunctionIntroduction hbase hstep⟩
  have h := InternalListInductionProof.actualOriginalListInductionAtCode body α Gamma theta code hp
  dsimp only [theta] at h
  rw [rowAtCode] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftInductionProof
