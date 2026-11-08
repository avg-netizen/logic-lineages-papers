module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftWitnessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalPathChecker InternalApplicationPathLift InternalApplicationPathLiftSyntaxProof
open InternalApplicationPathLiftSupportProof InternalApplicationPathLiftWitnessProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalPathCheckerProof InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Instantiate the five genuine universal binders of the tail invariant. -/
theorem rowApply (edge : Program 3) (vertex invariant : Program 5) (ps : Parameters α)
    (x y code out other mapped : OTerm α)
    (hr : Nonempty (Derivation body Gamma (row edge vertex invariant ps code)))
    (hi : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant false ps x y code out other mapped))) :
    Nonempty (Derivation body Gamma (pathGraph edge out other mapped)) := by
  obtain ⟨hr⟩ := actualFiniteUniversalElimination body α 5 Gamma
    (matrix edge vertex invariant ps code) (fun i => emb (![x,y,out,other,mapped] i)) hr
  rw [matrixWitness] at hr
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination hr hi⟩

/-- A single checked source edge transports the arithmetic invariant and its
actual lifted certificate. The tail uses only the internally quantified IH. -/
theorem consKnown (edge : Program 3) (vertex invariant : Program 5)
    (hInvariant : InvariantPreservation body edge invariant)
    (hEdge : EdgeCompatibility body edge vertex invariant)
    (positive : Bool) (ps : Parameters α)
    (x y code out other mapped raw tail v certificate mv mc mr mt : OTerm α)
    (hr : Nonempty (Derivation body Gamma (row edge vertex invariant ps tail)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode code raw tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw v certificate)))
    (hv : Nonempty (Derivation body Gamma (vertexAt vertex ps mv v)))
    (he : Nonempty (Derivation body Gamma (liftedEdgeAt ps mc certificate)))
    (hmp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing mr mv mc)))
    (hmt : Nonempty (Derivation body Gamma (mappedAt vertex ps mt tail)))
    (hmc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode mapped mr mt)))
    (hi : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant positive ps x y code out other mapped))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) out other mapped)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hs⟩ := consEquation (body := body) edge positive x y code raw tail v certificate hp hc
  have hsource := Derivation.implicationElimination (Derivation.conjunctionLeft hs)
    (Derivation.conjunctionLeft (Derivation.conjunctionRight hi))
  obtain ⟨hiv⟩ := closedApply (hInvariant α ps x v certificate)
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hi)
      (Derivation.conjunctionLeft hsource)⟩
  obtain ⟨hv⟩ := hv
  obtain ⟨he⟩ := he
  obtain ⟨hlift⟩ := closedApply (hEdge α ps x v certificate out mv mc)
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hi)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hsource)
        (Derivation.conjunctionIntroduction
          (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))
          (Derivation.conjunctionIntroduction hv he)))⟩
  obtain ⟨hmt⟩ := hmt
  have htailInputs : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant false ps v y tail mv other mt)) :=
    ⟨Derivation.conjunctionIntroduction hiv
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight hsource)
        (Derivation.conjunctionIntroduction hv
          (Derivation.conjunctionIntroduction
            (Derivation.conjunctionLeft (Derivation.conjunctionRight
              (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))) hmt)))⟩
  obtain ⟨htail⟩ := rowApply edge vertex invariant ps v y tail mv other mt hr htailInputs
  obtain ⟨htarget⟩ := consEquation (body := body) edge positive out other mapped mr mt mv mc hmp hmc
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight htarget)
    (Derivation.conjunctionIntroduction hlift htail)⟩

/-- The entry and mapped-tail witnesses come from the original arithmetic
programs, then disappear by existential elimination in the same calculus. -/
theorem consLift (edge : Program 3) (vertex invariant : Program 5)
    (hInvariant : InvariantPreservation body edge invariant)
    (hEdge : EdgeCompatibility body edge vertex invariant)
    (positive : Bool) (ps : Parameters α)
    (x y code out other mapped raw tail : OTerm α)
    (hr : Nonempty (Derivation body Gamma (row edge vertex invariant ps tail)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode code raw tail)))
    (hi : Nonempty (Derivation body Gamma
      (inputs edge vertex invariant positive ps x y code out other mapped))) :
    Nonempty (Derivation body Gamma (checkerGraph edge positive (suc z) out other mapped)) := by
  have hm : Nonempty (Derivation body Gamma (mappedAt vertex ps mapped code)) := by
    obtain ⟨hi⟩ := hi
    exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))⟩
  apply mappedConsCases vertex ps code raw tail mapped _ hc hm
  intro β j Delta v certificate mv mc mr mt hj hp hv he hmp hmt hmc
  rw [checkerRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  have hr' := renameInto hr j Delta hj
  rw [rowRename] at hr'
  have hc' := renameInto hc j Delta hj
  rw [graph2Rename] at hc'
  have hi' := renameInto hi j Delta hj
  rw [inputsRename] at hi'
  exact consKnown edge vertex invariant hInvariant hEdge positive (fun i => (ps i).relabel j)
    (x.relabel j) (y.relabel j) (code.relabel j) (out.relabel j) (other.relabel j)
    (mapped.relabel j) (raw.relabel j) (tail.relabel j) v certificate mv mc mr mt
    hr' hc' hp hv he hmp hmt hmc hi'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftCoreProof
