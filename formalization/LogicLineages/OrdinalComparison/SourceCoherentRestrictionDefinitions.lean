module
public import LogicLineages.OrdinalComparison.SourceCoherentTablesProof
@[expose] public section
/-! Literal restriction/reindexing of coherent table families. The complete
carrier is the independently constructed one, not a supplied closure field. -/
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentRestriction
open SourceCoherentTables

def pullbackDiagram {I J : Type} {A B : I → Type} [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (φ : J → I) : Diagram J (fun j => A (φ j)) (fun j => B (φ j)) where
  extension j k := D.extension (φ j) (φ k)
  inputMap j k h := D.inputMap (φ j) (φ k) h
  outputMap j k h := D.outputMap (φ j) (φ k) h

def rawRestriction {I J : Type} {A B : I → Type} (φ : J → I) (f : Raw I A B) :
    Raw J (fun j => A (φ j)) (fun j => B (φ j)) := fun j x => f (φ j) x

end LogicLineages.OrdinalComparison.Source.SourceCoherentRestriction
