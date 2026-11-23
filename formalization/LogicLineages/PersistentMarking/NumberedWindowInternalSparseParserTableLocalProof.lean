module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserTableLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalListCodec (consCode headCode tailCode)
open ID1Completion.InternalApplicationCertificateConstructors (graph1)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryRecover unaryRecover)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalRawListRecursionSupportProof (recursionRecover consTail)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchBase scratchStep scratchTable scratchRow)

abbrev tableReport {α : Type} (B : Program 2) (R : Program 4) (out index : OTerm α)
    (params : Fin 2 → OTerm α) : Formula α :=
  programGraph (scratchTable B R) out (Fin.cons index params)

abbrev rowReport {α : Type} (B : Program 2) (R : Program 4) (out index : OTerm α)
    (params : Fin 2 → OTerm α) : Formula α :=
  programGraph (scratchRow B R) out (Fin.cons index params)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- From adjacent actual table reports, the physical tail of the successor
table is its exact prior table. The new row is existentially opened in the
original graph calculus. All input ASTs are the actual parser definitions. -/
theorem exact_OriginalSparseParserTableTail (B : Program 2) (R : Program 4)
    (old next index : OTerm α) (params : Fin 2 → OTerm α)
    (before : Nonempty (Derivation body Γ (tableReport B R old index params)))
    (after : Nonempty (Derivation body Γ (tableReport B R next (suc index) params))) :
    Nonempty (Derivation body Γ (graph1 tailCode old next)) := by
  have step := recursionRecover (scratchBase B) (scratchStep R) next old index params before after
  apply programCases R (Fin.cons index (Fin.cons old params)) _
  intro β j Δ head keep picked
  rw [graph1Rename]
  simp only [consTermRename] at picked
  have moved := renameInto step j Δ keep
  simp only [programRename,consTermRename] at moved
  let xs : Fin 4 → OTerm β := Fin.cons (index.relabel j)
    (Fin.cons (old.relabel j) (fun i => (params i).relabel j))
  have cons := binaryRecover consCode R (.projection 1) (next.relabel j) head
    (old.relabel j) xs moved picked (projectionValue 1 xs)
  exact consTail (next.relabel j) head (old.relabel j) cons

/-- Recover the actual head-program observation from one original parser
row and the same-index, same-parameter literal table report. -/
theorem exact_OriginalSparseParserTableHead (B : Program 2) (R : Program 4)
    (out table index : OTerm α) (params : Fin 2 → OTerm α)
    (row : Nonempty (Derivation body Γ (rowReport B R out index params)))
    (stored : Nonempty (Derivation body Γ (tableReport B R table index params))) :
    Nonempty (Derivation body Γ (graph1 headCode out table)) :=
  unaryRecover headCode (scratchTable B R) out table (Fin.cons index params) row stored

#print axioms exact_OriginalSparseParserTableTail
#print axioms exact_OriginalSparseParserTableHead

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserTableLocalProof
