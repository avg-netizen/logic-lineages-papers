module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename emptyRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryRename)

abbrev rowGraph {α : Type} (o n : OTerm α) := programGraph (scratchRow parserBase parserStep) o ![n,z,z]
abbrev tableGraph {α : Type} (o n : OTerm α) := programGraph (scratchTable parserBase parserStep) o ![n,z,z]
abbrev stepGraph {α : Type} (o i v : OTerm α) := programGraph parserStep o ![i,v,z,z]
abbrev prependGraph {α : Type} (o h r : OTerm α) := programGraph prependResult o ![h,r]

theorem binaryInputsRename {α β : Type} (x y : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![x,y] : Fin 2 → OTerm α) i).relabel j) = ![x.relabel j,y.relabel j] := by
  simp only [consTermRename,emptyRename]

theorem tripleInputsRename {α β : Type} (x y w : OTerm α) (j : α → β) :
    (fun i : Fin 3 => ((![x,y,w] : Fin 3 → OTerm α) i).relabel j) =
      ![x.relabel j,y.relabel j,w.relabel j] := by
  simp only [consTermRename,emptyRename]

theorem quadInputsRename {α β : Type} (x y w b : OTerm α) (j : α → β) :
    (fun i : Fin 4 => ((![x,y,w,b] : Fin 4 → OTerm α) i).relabel j) =
      ![x.relabel j,y.relabel j,w.relabel j,b.relabel j] := by
  simp only [consTermRename,emptyRename]

theorem parserRename {α β : Type} (o n : OTerm α) (j : α → β) :
    (parserGraph o n).relabel j = parserGraph (o.relabel j) (n.relabel j) :=
  unaryRename parser o n j

theorem rowRename {α β : Type} (o n : OTerm α) (j : α → β) :
    (rowGraph o n).relabel j = rowGraph (o.relabel j) (n.relabel j) := by
  simp only [rowGraph,programRename,tripleInputsRename,zRelabel]

theorem tableRename {α β : Type} (o n : OTerm α) (j : α → β) :
    (tableGraph o n).relabel j = tableGraph (o.relabel j) (n.relabel j) := by
  simp only [tableGraph,programRename,tripleInputsRename,zRelabel]

theorem stepRename {α β : Type} (o i v : OTerm α) (j : α → β) :
    (stepGraph o i v).relabel j = stepGraph (o.relabel j) (i.relabel j) (v.relabel j) := by
  simp only [stepGraph,programRename,quadInputsRename,zRelabel]

theorem prependRename {α β : Type} (o h r : OTerm α) (j : α → β) :
    (prependGraph o h r).relabel j = prependGraph (o.relabel j) (h.relabel j) (r.relabel j) := by
  simp only [prependGraph,programRename,binaryInputsRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem parserArgs (n : OTerm α) :
    ∀ i : Fin 3, Nonempty (Derivation body Γ (programGraph
      ((![.projection 0,constantZero 1,constantZero 1] : Fin 3 → Program 1) i)
      ((![n,z,z] : Fin 3 → OTerm α) i) ![n])) := by
  intro i
  exact Fin.cases (projectionValue 0 ![n])
    (Fin.cases (zeroConstantValue ![n]) (Fin.cases (zeroConstantValue ![n]) (fun k => Fin.elim0 k))) i

theorem parserOfRow (o n : OTerm α)
    (h : Nonempty (Derivation body Γ (rowGraph o n))) :
    Nonempty (Derivation body Γ (parserGraph o n)) :=
  compositionValue (scratchRow parserBase parserStep) ![.projection 0,constantZero 1,constantZero 1]
    o ![n] ![n,z,z] h (parserArgs n)

theorem rowOfParser (o n : OTerm α)
    (h : Nonempty (Derivation body Γ (parserGraph o n))) :
    Nonempty (Derivation body Γ (rowGraph o n)) :=
  compositionRecover (scratchRow parserBase parserStep) ![.projection 0,constantZero 1,constantZero 1]
    o ![n] ![n,z,z] h (parserArgs n)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
