module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationPathMap InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem entryVertexValue (vertexProgram : Program 5)
    (context domain codomain argument raw value mappedValue : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left value raw)))
    (hv : Nonempty (Derivation body Gamma
      (programGraph vertexProgram mappedValue (vertexArguments context domain codomain argument value)))) :
    Nonempty (Derivation body Gamma
      (programGraph (entryVertex vertexProgram) mappedValue
        (Fin.cons raw (parameters context domain codomain argument)))) := by
  let xs : Fin 5 → OTerm α := Fin.cons raw (parameters context domain codomain argument)
  apply compositionValue vertexProgram
    ![.projection 1,.projection 2,.projection 3,.projection 4,leftOf (.projection 0)]
    mappedValue xs (vertexArguments context domain codomain argument value) hv
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 4 xs)
      (Fin.cases (unaryValue InternalUnpair.left (.projection 0) value raw xs hl
        (projectionValue 0 xs)) (fun q => Fin.elim0 q))))) i

theorem entryEdgeValue (context domain codomain argument raw edge mappedEdge : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right edge raw)))
    (he : Nonempty (Derivation body Gamma
      (graph4 InternalApplicationCertificateConstructors.edgeLift mappedEdge domain codomain argument edge))) :
    Nonempty (Derivation body Gamma
      (programGraph entryEdge mappedEdge
        (Fin.cons raw (parameters context domain codomain argument)))) := by
  let xs : Fin 5 → OTerm α := Fin.cons raw (parameters context domain codomain argument)
  apply compositionValue InternalApplicationCertificateConstructors.edgeLift
    ![.projection 2,.projection 3,.projection 4,rightOf (.projection 0)]
    mappedEdge xs (Fin.cons domain (Fin.cons codomain (Fin.cons argument (Fin.cons edge Fin.elim0)))) he
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
    (Fin.cases (projectionValue 4 xs)
      (Fin.cases (unaryValue InternalUnpair.right (.projection 0) edge raw xs hr
        (projectionValue 0 xs)) (fun q => Fin.elim0 q)))) i

theorem entryComponents (vertexProgram : Program 5)
    (context domain codomain argument raw value edge mappedValue mappedEdge : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (entryPremises vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge))) :
    Nonempty (Derivation body Gamma
      (programGraph (entryVertex vertexProgram) mappedValue
        (Fin.cons raw (parameters context domain codomain argument)))) ∧
    Nonempty (Derivation body Gamma
      (programGraph entryEdge mappedEdge
        (Fin.cons raw (parameters context domain codomain argument)))) := by
  obtain ⟨h⟩ := h
  have hp := Nonempty.intro (Derivation.conjunctionLeft h)
  exact ⟨entryVertexValue vertexProgram context domain codomain argument raw value mappedValue
      (pairLeft raw value edge hp)
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩,
    entryEdgeValue context domain codomain argument raw edge mappedEdge
      (pairRight raw value edge hp)
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩⟩

theorem entryForward (vertexProgram : Program 5)
    (context domain codomain argument raw value edge mappedValue mappedEdge out : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (entryPremises vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge)))
    (he : Nonempty (Derivation body Gamma
      (entryGraph vertexProgram out raw context domain codomain argument))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out mappedValue mappedEdge)) := by
  obtain ⟨hv,hk⟩ := entryComponents vertexProgram context domain codomain argument raw value edge
    mappedValue mappedEdge hp
  exact binaryRecover InternalPairing.pairing (entryVertex vertexProgram) entryEdge out mappedValue mappedEdge
    (Fin.cons raw (parameters context domain codomain argument)) he hv hk

theorem entryBackward (vertexProgram : Program 5)
    (context domain codomain argument raw value edge mappedValue mappedEdge out : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (entryPremises vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge)))
    (he : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out mappedValue mappedEdge))) :
    Nonempty (Derivation body Gamma
      (entryGraph vertexProgram out raw context domain codomain argument)) := by
  obtain ⟨hv,hk⟩ := entryComponents vertexProgram context domain codomain argument raw value edge
    mappedValue mappedEdge hp
  exact binaryValue InternalPairing.pairing (entryVertex vertexProgram) entryEdge out mappedValue mappedEdge
    (Fin.cons raw (parameters context domain codomain argument)) he hv hk

theorem actualOriginalEntryGraphEquation :
    InternalApplicationPathMapTargets.ActualOriginalEntryGraphEquation := by
  intro body vertexProgram α context domain codomain argument raw value edge mappedValue mappedEdge out
  apply InternalApplicationCertificateConstructorsProof.guardedIff
  · exact entryForward vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact entryBackward vertexProgram context domain codomain argument raw value edge mappedValue mappedEdge out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalPathMapZero :
    InternalApplicationPathMapTargets.ActualOriginalPathMapZero := by
  intro body vertexProgram α out context domain codomain argument
  exact InternalListMapProof.actualOriginalListMapZero body 4 (entry vertexProgram) α out
    (parameters context domain codomain argument)

theorem actualOriginalPathMapCons :
    InternalApplicationPathMapTargets.ActualOriginalPathMapCons := by
  intro body vertexProgram α context domain codomain argument code raw tail value edge
    mappedValue mappedEdge mappedRaw mappedTail out
  let P := consPremises vertexProgram context domain codomain argument code raw tail value edge
    mappedValue mappedEdge mappedRaw mappedTail
  have hp : Derivation body [P] P := Derivation.hypothesis List.mem_cons_self
  have hcons := Derivation.conjunctionLeft hp
  have hentry := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight hp))
  have hpair := Nonempty.intro
    (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hp)))
  have htail := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hp))
  obtain ⟨he⟩ := entryBackward vertexProgram context domain codomain argument raw value edge
    mappedValue mappedEdge mappedRaw hentry hpair
  obtain ⟨h⟩ := closedApply
    (InternalListMapProof.actualOriginalListMapCons body 4 (entry vertexProgram) α
      code raw tail mappedRaw mappedTail out (parameters context domain codomain argument))
    ⟨Derivation.conjunctionIntroduction hcons (Derivation.conjunctionIntroduction he htail)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapProof
