module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassReadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInterfaceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxClassTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralAuxClassLeastProof (functionClass argumentClass)
open NumberedWindowInternalLiteralAuxClassReadProof (exact_OpenLiteralFunctionClass exact_OpenLiteralArgumentClass)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consEqual (x y u v : OTerm α)
    (first : Nonempty (Derivation B Γ (eqn x u)))
    (second : Nonempty (Derivation B Γ (eqn y v))) :
    Nonempty (Derivation B Γ (eqn (rawCons x y) (rawCons u v))) := by
  let before : Fin 2 → OTerm α := ![x,y]
  let after : Fin 2 → OTerm α := ![u,v]
  have input (i : Fin 2) :
      Nonempty (Derivation B Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases first (Fin.cases second (fun n => Fin.elim0 n)) i
  have old : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) before)) :=
    consGraph x y
  unfold programGraph at old
  have moved : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) after)) := by
    unfold programGraph
    exact graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (rawCons x y) before after input old
  exact valueUnique fieldCons (rawCons x y) (rawCons u v) after moved (consGraph u v)


private theorem queryMove (K : Program 3) (ctx ty q ty' q' value : OTerm α)
    (typeEq : D B Γ (eqn ty ty')) (same : D B Γ (eqn q q'))
    (held : D B Γ (programGraph K value ![ctx,ty,q])) :
    D B Γ (programGraph K value ![ctx,ty',q']) := by
  unfold programGraph at *
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula K) value ![ctx,ty,q] ![ctx,ty',q'] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx))
    (Fin.cases typeEq (Fin.cases same (fun n => Fin.elim0 n))) i

theorem exact_OpenTypedAuxFunctionClassTransport (E : Program 4) (K : Program 3) (stable : Preserves E K)
    (ctx value : OTerm α) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (edge : D B Γ (childAlternatives E ctx a b))
    (source : D B Γ (programGraph (functionClass K) value ![ctx,a.term])) :
    D B Γ (programGraph (functionClass K) value ![ctx,b.term]) := by
  let F := acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg
  have first := (exact_OpenLiteralFunctionClass K ctx a.dom a.cod a.fn a.arg value).2 source
  obtain ⟨report⟩ := first
  obtain ⟨typeEq⟩ := consEqual a.dom a.cod b.dom b.cod dom cod
  obtain ⟨split⟩ := edge
  have left : D B (F :: Γ) (programGraph (functionClass K) value ![ctx,b.term]) := by
    have prem : Derivation B (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
    have carried := stable B α (F :: Γ) ctx (rawCons a.dom a.cod) a.fn b.fn value
      ⟨Derivation.conjunctionLeft prem⟩ ⟨addHyp report F⟩
    have move := queryMove K ctx (rawCons a.dom a.cod) b.fn (rawCons b.dom b.cod) b.fn value
      ⟨addHyp typeEq F⟩ ⟨refl b.fn⟩ carried
    exact (exact_OpenLiteralFunctionClass K ctx b.dom b.cod b.fn b.arg value).1 move
  have right : D B (A :: Γ) (programGraph (functionClass K) value ![ctx,b.term]) := by
    have prem : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
    have move := queryMove K ctx (rawCons a.dom a.cod) a.fn (rawCons b.dom b.cod) b.fn value
      ⟨addHyp typeEq A⟩ ⟨Derivation.conjunctionLeft prem⟩ ⟨addHyp report A⟩
    exact (exact_OpenLiteralFunctionClass K ctx b.dom b.cod b.fn b.arg value).1 move
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

theorem exact_OpenTypedAuxArgumentClassTransport (E : Program 4) (K : Program 3) (stable : Preserves E K)
    (ctx value : OTerm α) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (edge : D B Γ (childAlternatives E ctx a b))
    (source : D B Γ (programGraph (argumentClass K) value ![ctx,a.term])) :
    D B Γ (programGraph (argumentClass K) value ![ctx,b.term]) := by
  let F := acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg
  obtain ⟨report⟩ := (exact_OpenLiteralArgumentClass K ctx a.dom a.cod a.fn a.arg value).2 source
  obtain ⟨typeEq⟩ := dom
  obtain ⟨split⟩ := edge
  have left : D B (F :: Γ) (programGraph (argumentClass K) value ![ctx,b.term]) := by
    have prem : Derivation B (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
    have move := queryMove K ctx a.dom a.arg b.dom b.arg value
      ⟨addHyp typeEq F⟩ ⟨Derivation.conjunctionRight prem⟩ ⟨addHyp report F⟩
    exact (exact_OpenLiteralArgumentClass K ctx b.dom b.cod b.fn b.arg value).1 move
  have right : D B (A :: Γ) (programGraph (argumentClass K) value ![ctx,b.term]) := by
    have prem : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
    have carried := stable B α (A :: Γ) ctx a.dom a.arg b.arg value
      ⟨Derivation.conjunctionRight prem⟩ ⟨addHyp report A⟩
    have move := queryMove K ctx a.dom b.arg b.dom b.arg value ⟨addHyp typeEq A⟩ ⟨refl b.arg⟩ carried
    exact (exact_OpenLiteralArgumentClass K ctx b.dom b.cod b.fn b.arg value).1 move
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

#print axioms exact_OpenTypedAuxFunctionClassTransport
#print axioms exact_OpenTypedAuxArgumentClassTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxClassTransportProof
