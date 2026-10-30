module
public import LogicLineages.OrdinalComparison.SourceCoherentRestrictionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentRestrictionTargets
open SourceCoherentTables SourceCoherentTablesProof SourceCoherentRestriction

def RestrictionCoherence : Prop := ∀ (I J : Type) (A B : I → Type)
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (φ : J → I) (f : Raw I A B),
    Coherent D f → Coherent (pullbackDiagram D φ) (rawRestriction φ f)

def RawRestrictionLattice : Prop := ∀ (I J : Type) (A B : I → Type)
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (φ : J → I) (S : Set (Raw I A B)),
    rawRestriction φ (sSup S) = sSup (rawRestriction φ '' S) ∧
    rawRestriction φ (sInf S) = sInf (rawRestriction φ '' S)

def ActualCoherentRestrictionHom : Prop := ∀ (I J : Type) (A B : I → Type)
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    (D : Diagram I A B) (φ : J → I),
    ∃ h : CompleteLatticeHom (coherentSublattice D) (coherentSublattice (pullbackDiagram D φ)),
      ∀ f, (h f).val = rawRestriction φ f.val

def FiniteRestrictionMembership : Prop := ∀ (I J : Type) (A B : I → Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) (φ : J → I) (f : Raw I A B),
    f ∈ finiteTables D → rawRestriction φ f ∈ finiteTables (pullbackDiagram D φ)

end LogicLineages.OrdinalComparison.Source.SourceCoherentRestrictionTargets
