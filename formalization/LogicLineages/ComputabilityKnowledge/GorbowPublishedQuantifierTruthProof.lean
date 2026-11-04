module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthTargets
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatchProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof

@[expose] public section
/-! Named source dispatch on the real published-D ground, and the literal
coded quantifier/UBF axioms at its positive revision stages. Each listed
named header is reduced through the actual named dispatcher and the
calibrated source programs; the finite RelationLaws/FunctionLaws are then
derived from those equations and the source dispatch numbers, and the paid
ground-generic quantifier theorem is applied to them. No identity of whole
grounds and no malformed-header claim is made. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.Proof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowPublishedModel GorbowRegistryTuple

attribute [local irreducible] GorbowRegistryTuple.header

/-! ### Listed named headers -/

theorem namedFunctions : GorbowPublishedQuantifierTruth.Targets.NamedFunctions := by
  intro pF pR q c hA name hn args hlen
  have hF := (GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1).1
  exact (GorbowNamedRegistryInterpretation.Proof.namedFunction (augmented pF q) pR name hn
    args hlen).trans (hF _)

theorem namedRelations : GorbowPublishedQuantifierTruth.Targets.NamedRelations := by
  intro pF pR q c hA name hn args hlen
  have h1 := GorbowNamedRegistryInterpretation.Proof.namedRelation (augmented pF q) pR name hn
    args hlen
  rw [hA.1.2] at h1
  refine h1.trans ?_
  unfold GorbowSourceRegistryPadding.sourceRelationValue
  cases GorbowSortedRegistry.relationProgram (header name.1 name.2 args) <;> simp

/-! ### Finite source dispatch laws, derived on the actual ground -/

private theorem relationLaws (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : GorbowRegistryDispatch.RelationLaws (ground pF pR q) := by
  intro a b
  obtain ⟨h0, h1, h2, h3, h4⟩ := GorbowSortedRegistryProof.relationDispatch a b
  have r0 : (ground pF pR q).universalRelation (header 1 0 [a]) ↔
      GorbowSortedRegistry.relationProgram (header 1 0 [a]) = true :=
    namedRelations pF pR q c hA (1, 0) (by simp [GorbowSourceRegistryPadding.relationNames]) [a] rfl
  have r1 : (ground pF pR q).universalRelation (header 1 1 [a]) ↔
      GorbowSortedRegistry.relationProgram (header 1 1 [a]) = true :=
    namedRelations pF pR q c hA (1, 1) (by simp [GorbowSourceRegistryPadding.relationNames]) [a] rfl
  have r2 : (ground pF pR q).universalRelation (header 1 2 [a]) ↔
      GorbowSortedRegistry.relationProgram (header 1 2 [a]) = true :=
    namedRelations pF pR q c hA (1, 2) (by simp [GorbowSourceRegistryPadding.relationNames]) [a] rfl
  have r3 : (ground pF pR q).universalRelation (header 1 3 [a]) ↔
      GorbowSortedRegistry.relationProgram (header 1 3 [a]) = true :=
    namedRelations pF pR q c hA (1, 3) (by simp [GorbowSourceRegistryPadding.relationNames]) [a] rfl
  have r4 : (ground pF pR q).universalRelation (header 2 0 [a, b]) ↔
      GorbowSortedRegistry.relationProgram (header 2 0 [a, b]) = true :=
    namedRelations pF pR q c hA (2, 0) (by simp [GorbowSourceRegistryPadding.relationNames])
      [a, b] rfl
  rw [h0] at r0
  rw [h1] at r1
  rw [h2] at r2
  rw [h3] at r3
  rw [h4] at r4
  exact ⟨r0, r1, r2, r3, r4⟩

private theorem functionLaws (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : GorbowRegistryDispatch.FunctionLaws (ground pF pR q) := by
  intro a b c'
  obtain ⟨d0, d1, d2, d3, d4, d5, d6⟩ := GorbowDiagonalRegistryProof.originalDispatch.2 a b c'
  have f0 : (ground pF pR q).universalFunction (header 1 0 [a]) =
      GorbowSourceRegistryPadding.sourceFunction (header 1 0 [a]) :=
    namedFunctions pF pR q c hA (1, 0) (by simp [GorbowSourceRegistryPadding.functionNames]) [a] rfl
  have f1 : (ground pF pR q).universalFunction (header 2 0 [a, b]) =
      GorbowSourceRegistryPadding.sourceFunction (header 2 0 [a, b]) :=
    namedFunctions pF pR q c hA (2, 0) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b] rfl
  have f2 : (ground pF pR q).universalFunction (header 2 1 [a, b]) =
      GorbowSourceRegistryPadding.sourceFunction (header 2 1 [a, b]) :=
    namedFunctions pF pR q c hA (2, 1) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b] rfl
  have f3 : (ground pF pR q).universalFunction (header 2 2 [a, b]) =
      GorbowSourceRegistryPadding.sourceFunction (header 2 2 [a, b]) :=
    namedFunctions pF pR q c hA (2, 2) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b] rfl
  have f4 : (ground pF pR q).universalFunction (header 2 3 [a, b]) =
      GorbowSourceRegistryPadding.sourceFunction (header 2 3 [a, b]) :=
    namedFunctions pF pR q c hA (2, 3) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b] rfl
  have f5 : (ground pF pR q).universalFunction (header 2 4 [a, b]) =
      GorbowSourceRegistryPadding.sourceFunction (header 2 4 [a, b]) :=
    namedFunctions pF pR q c hA (2, 4) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b] rfl
  have f6 : (ground pF pR q).universalFunction (header 3 0 [a, b, c']) =
      GorbowSourceRegistryPadding.sourceFunction (header 3 0 [a, b, c']) :=
    namedFunctions pF pR q c hA (3, 0) (by simp [GorbowSourceRegistryPadding.functionNames])
      [a, b, c'] rfl
  exact ⟨f0.trans d0, f1.trans d1, f2.trans d2, f3.trans d3, f4.trans d4, f5.trans d5,
    f6.trans d6⟩

theorem sourceDispatch : GorbowPublishedQuantifierTruth.Targets.SourceDispatch := by
  intro pF pR q c hA
  exact ⟨relationLaws pF pR q c hA, functionLaws pF pR q c hA⟩

/-! ### Coded quantifier FS and UBF at actual positive stages -/

theorem positiveQuantifierAxioms :
    GorbowPublishedQuantifierTruth.Targets.PositiveQuantifierAxioms := by
  intro pF pR q c hA k
  obtain ⟨hr, hf⟩ := sourceDispatch pF pR q c hA
  exact GorbowRegistryDispatchProof.gorbowRegistryDispatch.2.2 (ground pF pR q) hr hf
    (theoremCodes pF pR q c) k

theorem fullTarget : GorbowPublishedQuantifierTruth.Targets.Target :=
  ⟨namedFunctions, namedRelations, sourceDispatch, positiveQuantifierAxioms⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruth.Proof
