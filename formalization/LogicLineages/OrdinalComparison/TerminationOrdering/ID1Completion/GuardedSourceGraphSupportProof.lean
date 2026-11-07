module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGraphSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GuardedSource InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceBranchProof InternalControlGraphSupportProof InternalGraphCompositionEqualityProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem tupleOneRename {β : Type} (a : OTerm α) (j : α → β) :
    (fun i => (![a] i).relabel j) = ![a.relabel j] := by
  funext i
  exact Fin.cases rfl (fun q => Fin.elim0 q) i

@[simp] theorem tupleTwoRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i => (![a,b] i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

@[simp] theorem tupleThreeRename {β : Type} (a b c : OTerm α) (j : α → β) :
    (fun i => (![a,b,c] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

@[simp] theorem tupleFourRename {β : Type} (a b c d : OTerm α) (j : α → β) :
    (fun i => (![a,b,c,d] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem typedTagValue (tag : Program 2) (a c typ x : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph tag a ![c,x]))) :
    Nonempty (Derivation body Gamma (programGraph (typedTag tag) a ![c,typ,x])) := by
  apply compositionValue tag ![.projection 0,.projection 2] a ![c,typ,x] ![c,x] h
  intro i
  exact Fin.cases (projectionValue 0 ![c,typ,x])
    (Fin.cases (projectionValue 2 ![c,typ,x]) (fun q => Fin.elim0 q)) i

theorem typedMatchAccept (tag : Program 2) (a c typ x : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (he : Nonempty (Derivation body Gamma (eqn typ a))) :
    Nonempty (Derivation body Gamma (programGraph (typedMatch tag) (suc z) ![c,typ,x])) := by
  apply compositionValue InternalEqualityTest.equalityTest ![.projection 1,typedTag tag]
    (suc z) ![c,typ,x] ![typ,a] (equalityOfEqual typ a he)
  intro i
  exact Fin.cases (projectionValue 1 ![c,typ,x])
    (Fin.cases (typedTagValue tag a c typ x ht) (fun q => Fin.elim0 q)) i

theorem typedMatchRecover (tag : Program 2) (a c typ x : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hm : Nonempty (Derivation body Gamma (programGraph (typedMatch tag) (suc z) ![c,typ,x]))) :
    Nonempty (Derivation body Gamma (eqn typ a)) := by
  apply equalityOfAcceptance typ a
  apply compositionRecover InternalEqualityTest.equalityTest ![.projection 1,typedTag tag]
    (suc z) ![c,typ,x] ![typ,a] hm
  intro i
  exact Fin.cases (projectionValue 1 ![c,typ,x])
    (Fin.cases (typedTagValue tag a c typ x ht) (fun q => Fin.elim0 q)) i

theorem guardedTypedAccept (typed : Program 3) (tag : Program 2) (a c typ x : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,typ,x])))
    (he : Nonempty (Derivation body Gamma (eqn typ a))) :
    Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,x])) :=
  conjunctionAccept typed (typedMatch tag) ![c,typ,x] hp (typedMatchAccept tag a c typ x ht he)

theorem guardedTypedRecover (typed : Program 3) (tag : Program 2) (a c typ x : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,x]))) :
    Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,typ,x] ⊓ eqn typ a)) := by
  obtain ⟨d⟩ := conjunctionRecover typed (typedMatch tag) ![c,typ,x] hp
  obtain ⟨e⟩ := typedMatchRecover tag a c typ x ht ⟨Derivation.conjunctionRight d⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft d) e⟩

theorem typedTypeTransport (typed : Program 3) (c s t x : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn s t)))
    (hp : Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,s,x]))) :
    Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,t,x])) := by
  apply graphInputTransport body α 3 Gamma _ (suc z) ![c,s,x] ![c,t,x] _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q))) i
  · rw [onEquality]; exact ⟨refl c⟩
  · rw [onEquality]; exact he
  · rw [onEquality]; exact ⟨refl x⟩

theorem leftTagValue (tag : Program 2) (a c x y k : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph tag a ![c,x]))) :
    Nonempty (Derivation body Gamma (programGraph (leftTag tag) a ![c,x,y,k])) := by
  apply compositionValue tag ![.projection 0,.projection 1] a ![c,x,y,k] ![c,x] h
  intro i
  exact Fin.cases (projectionValue 0 ![c,x,y,k])
    (Fin.cases (projectionValue 1 ![c,x,y,k]) (fun q => Fin.elim0 q)) i

theorem rightTagValue (tag : Program 2) (b c x y k : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph tag b ![c,y]))) :
    Nonempty (Derivation body Gamma (programGraph (rightTag tag) b ![c,x,y,k])) := by
  apply compositionValue tag ![.projection 0,.projection 2] b ![c,x,y,k] ![c,y] h
  intro i
  exact Fin.cases (projectionValue 0 ![c,x,y,k])
    (Fin.cases (projectionValue 2 ![c,x,y,k]) (fun q => Fin.elim0 q)) i

theorem sourceTypedAccept (typed : Program 3) (tag : Program 2) (a c x y k : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,a,x]))) :
    Nonempty (Derivation body Gamma (programGraph (sourceTyped typed tag) (suc z) ![c,x,y,k])) := by
  apply compositionValue typed ![.projection 0,leftTag tag,.projection 1]
    (suc z) ![c,x,y,k] ![c,a,x] hp
  intro i
  exact Fin.cases (projectionValue 0 ![c,x,y,k])
    (Fin.cases (leftTagValue tag a c x y k ht)
      (Fin.cases (projectionValue 1 ![c,x,y,k]) (fun q => Fin.elim0 q))) i

theorem targetTypedRecover (typed : Program 3) (tag : Program 2) (b c x y k : OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph tag b ![c,y])))
    (hp : Nonempty (Derivation body Gamma (programGraph (targetTyped typed tag) (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (programGraph typed (suc z) ![c,b,y])) := by
  apply compositionRecover typed ![.projection 0,rightTag tag,.projection 2]
    (suc z) ![c,x,y,k] ![c,b,y] hp
  intro i
  exact Fin.cases (projectionValue 0 ![c,x,y,k])
    (Fin.cases (rightTagValue tag b c x y k ht)
      (Fin.cases (projectionValue 2 ![c,x,y,k]) (fun q => Fin.elim0 q))) i

theorem sameTagRecover (tag : Program 2) (a b c x y k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hy : Nonempty (Derivation body Gamma (programGraph tag b ![c,y])))
    (hp : Nonempty (Derivation body Gamma (programGraph (sameTag tag) (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (eqn a b)) := by
  apply equalityOfAcceptance a b
  apply compositionRecover InternalEqualityTest.equalityTest ![leftTag tag,rightTag tag]
    (suc z) ![c,x,y,k] ![a,b] hp
  intro i
  exact Fin.cases (leftTagValue tag a c x y k hx)
    (Fin.cases (rightTagValue tag b c x y k hy) (fun q => Fin.elim0 q)) i

theorem windowAtAccept (window : Program 1) (c x y k : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph window (suc z) ![c]))) :
    Nonempty (Derivation body Gamma (programGraph (windowAt window) (suc z) ![c,x,y,k])) := by
  apply compositionValue window ![.projection 0] (suc z) ![c,x,y,k] ![c] h
  intro i
  exact Fin.cases (projectionValue 0 ![c,x,y,k]) (fun q => Fin.elim0 q) i

/-- Core source closure at explicit INTERNAL extractor outputs. -/
theorem certificateAtTags (typed : Program 3) (positive : Program 4)
    (tag : Program 2) (window : Program 1) (a b c typ x y k : OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph window (suc z) ![c])))
    (hx : Nonempty (Derivation body Gamma (programGraph tag a ![c,x])))
    (hy : Nonempty (Derivation body Gamma (programGraph tag b ![c,y])))
    (ht : Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma (programGraph (guardedPositive positive typed tag window)
      (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (programGraph (guardedTyped typed tag) (suc z) ![c,typ,y])) := by
  obtain ⟨d⟩ := guardedTypedRecover typed tag a c typ x hx ht
  have hs := typedTypeTransport typed c typ a x ⟨Derivation.conjunctionRight d⟩
    ⟨Derivation.conjunctionLeft d⟩
  have ha := conjunctionAccept (windowAt window) (sourceTyped typed tag) ![c,x,y,k]
    (windowAtAccept window c x y k hw) (sourceTypedAccept typed tag a c x y k hx hs)
  have hactive := successorBranchElim (activation typed tag window) positive
    (acceptedTarget positive typed tag) (suc z) z ![c,x,y,k] ha hp
  obtain ⟨dt⟩ := conjunctionRecover positive
    (conjunction (targetTyped typed tag) (sameTag tag)) ![c,x,y,k] hactive
  obtain ⟨dg⟩ := conjunctionRecover (targetTyped typed tag) (sameTag tag) ![c,x,y,k]
    ⟨Derivation.conjunctionRight dt⟩
  have htarget := targetTypedRecover typed tag b c x y k hy ⟨Derivation.conjunctionLeft dg⟩
  obtain ⟨he⟩ := sameTagRecover tag a b c x y k hx hy ⟨Derivation.conjunctionRight dg⟩
  have htype : Nonempty (Derivation body Gamma (eqn typ b)) :=
    ⟨trans (Derivation.conjunctionRight d) he⟩
  obtain ⟨htype'⟩ := htype
  exact guardedTypedAccept typed tag b c typ y hy
    (typedTypeTransport typed c b typ y ⟨symm htype'⟩ htarget) ⟨htype'⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGraphSupportProof
