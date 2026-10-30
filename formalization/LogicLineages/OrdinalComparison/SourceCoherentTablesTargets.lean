module
public import LogicLineages.OrdinalComparison.SourceCoherentTablesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentTablesTargets
open SourceCoherentTables

def CoherentValidityTest : Prop := ∀ (I : Type) (A B : I → Type) [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) (f : Raw I A B), validityTest D f = true ↔ Coherent D f

def CoherentFiniteEnumeration : Prop := ∀ (I : Type) (A B : I → Type) [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) (f : Raw I A B), f ∈ finiteTables D ↔ Coherent D f

def CoherentArbitraryClosure : Prop := ∀ (I : Type) (A B : I → Type)
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (S : Set (Raw I A B)), (∀ f ∈ S, Coherent D f) →
      Coherent D (sSup S) ∧ Coherent D (sInf S)

def ActualCoherentSublattice : Prop := ∀ (I : Type) (A B : I → Type)
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B), ∃ L : CompleteSublattice (Raw I A B),
      ∀ f, f ∈ L ↔ Coherent D f

def FiniteCoherentCarrier : Prop := ∀ (I : Type) (A B : I → Type) [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B), Finite {f : Raw I A B // Coherent D f}

end LogicLineages.OrdinalComparison.Source.SourceCoherentTablesTargets
