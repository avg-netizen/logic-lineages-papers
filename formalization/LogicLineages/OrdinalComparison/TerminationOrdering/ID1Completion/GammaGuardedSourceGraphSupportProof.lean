module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceGraphSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GammaGuardedSource GammaGuardedSourceBranchProof GuardedSourceGraphSupportProof
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalEqualityTestProof InternalEqualityTestCompositionProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atInputValue {m : Nat} (p : Program 1) (i : Fin m)
    (out : OTerm α) (xs : Fin m → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph p out ![xs i]))) :
    Nonempty (Derivation body Gamma (programGraph (atInput p i) out xs)) := by
  apply compositionValue p ![.projection i] out xs ![xs i] h
  intro j
  exact Fin.cases (projectionValue i xs) (fun q => Fin.elim0 q) j

theorem atInputRecover {m : Nat} (p : Program 1) (i : Fin m)
    (out : OTerm α) (xs : Fin m → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (atInput p i) out xs))) :
    Nonempty (Derivation body Gamma (programGraph p out ![xs i])) := by
  apply compositionRecover p ![.projection i] out xs ![xs i] h
  intro j
  exact Fin.cases (projectionValue i xs) (fun q => Fin.elim0 q) j

theorem sameGammaAccept {m : Nat} (gamma : Program 1) (i j : Fin m)
    (a b : OTerm α) (xs : Fin m → OTerm α)
    (ha : Nonempty (Derivation body Gamma (programGraph gamma a ![xs i])))
    (hb : Nonempty (Derivation body Gamma (programGraph gamma b ![xs j])))
    (he : Nonempty (Derivation body Gamma (eqn a b))) :
    Nonempty (Derivation body Gamma (programGraph (sameGamma gamma i j) (suc z) xs)) := by
  apply compositionValue InternalEqualityTest.equalityTest ![atInput gamma i,atInput gamma j]
    (suc z) xs ![a,b] (equalityOfEqual a b he)
  intro k
  exact Fin.cases (atInputValue gamma i a xs ha)
    (Fin.cases (atInputValue gamma j b xs hb) (fun q => Fin.elim0 q)) k

/-- compositionRecover aligns all internally quantified Gamma values by
valueUnique before equality acceptance is inverted. -/
theorem sameGammaRecover {m : Nat} (gamma : Program 1) (i j : Fin m)
    (a b : OTerm α) (xs : Fin m → OTerm α)
    (ha : Nonempty (Derivation body Gamma (programGraph gamma a ![xs i])))
    (hb : Nonempty (Derivation body Gamma (programGraph gamma b ![xs j])))
    (he : Nonempty (Derivation body Gamma (programGraph (sameGamma gamma i j) (suc z) xs))) :
    Nonempty (Derivation body Gamma (eqn a b)) := by
  apply equalityOfAcceptance a b
  apply compositionRecover InternalEqualityTest.equalityTest ![atInput gamma i,atInput gamma j]
    (suc z) xs ![a,b] he
  intro k
  exact Fin.cases (atInputValue gamma i a xs ha)
    (Fin.cases (atInputValue gamma j b xs hb) (fun q => Fin.elim0 q)) k

theorem typedValid (typed : Program 3) (valid : Program 1) (tag : Program 2)
    (c typ x : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,x]))) :
    Nonempty (Derivation body Gamma (programGraph valid (suc z) ![x])) := by
  obtain ⟨d⟩ := conjunctionRecover (baseTyped typed valid) (GuardedSource.typedMatch tag) ![c,typ,x] ht
  obtain ⟨e⟩ := conjunctionRecover typed (atInput valid 2) ![c,typ,x]
    ⟨Derivation.conjunctionLeft d⟩
  exact atInputRecover valid 2 (suc z) ![c,typ,x] ⟨Derivation.conjunctionRight e⟩

theorem positiveGamma (positive : Program 4) (gamma : Program 1)
    (a b c x y k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hy : Nonempty (Derivation body Gamma (programGraph gamma b ![y])))
    (hp : Nonempty (Derivation body Gamma (programGraph (basePositive positive gamma)
      (suc z) ![c,x,y,k]))) :
    Nonempty (Derivation body Gamma (eqn a b)) := by
  obtain ⟨d⟩ := conjunctionRecover positive (sameGamma gamma 1 2) ![c,x,y,k] hp
  exact sameGammaRecover gamma 1 2 a b ![c,x,y,k] hx hy ⟨Derivation.conjunctionRight d⟩

theorem guardAccept (valid gamma : Program 1) (a b x u : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hu : Nonempty (Derivation body Gamma (programGraph gamma b ![u])))
    (hvx : Nonempty (Derivation body Gamma (programGraph valid (suc z) ![x])))
    (hvu : Nonempty (Derivation body Gamma (programGraph valid (suc z) ![u])))
    (he : Nonempty (Derivation body Gamma (eqn a b))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u])) :=
  conjunctionAccept (atInput valid 0) (conjunction (atInput valid 1) (sameGamma gamma 0 1)) ![x,u]
    (atInputValue valid 0 (suc z) ![x,u] hvx)
    (conjunctionAccept (atInput valid 1) (sameGamma gamma 0 1) ![x,u]
      (atInputValue valid 1 (suc z) ![x,u] hvu)
      (sameGammaAccept gamma 0 1 a b ![x,u] hx hu he))

theorem guardRecover (valid gamma : Program 1) (a b x u : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hu : Nonempty (Derivation body Gamma (programGraph gamma b ![u])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u]))) :
    Nonempty (Derivation body Gamma
      (programGraph valid (suc z) ![u] ⊓ eqn a b)) := by
  obtain ⟨d⟩ := conjunctionRecover (atInput valid 0)
    (conjunction (atInput valid 1) (sameGamma gamma 0 1)) ![x,u] hg
  obtain ⟨e⟩ := conjunctionRecover (atInput valid 1) (sameGamma gamma 0 1) ![x,u]
    ⟨Derivation.conjunctionRight d⟩
  obtain ⟨hv⟩ := atInputRecover valid 1 (suc z) ![x,u] ⟨Derivation.conjunctionLeft e⟩
  obtain ⟨he⟩ := sameGammaRecover gamma 0 1 a b ![x,u] hx hu ⟨Derivation.conjunctionRight e⟩
  exact ⟨Derivation.conjunctionIntroduction hv he⟩

/-- Original graph proof at explicit internal Gamma outputs. -/
theorem certificateAtValues (typed : Program 3) (positive : Program 4)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (a b d c typ x y u k : OTerm α)
    (hx : Nonempty (Derivation body Gamma (programGraph gamma a ![x])))
    (hy : Nonempty (Derivation body Gamma (programGraph gamma b ![y])))
    (hu : Nonempty (Derivation body Gamma (programGraph gamma d ![u])))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedTyped (baseTyped typed valid) tag) (suc z) ![c,typ,x])))
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive (basePositive positive gamma)
        (baseTyped typed valid) tag window) (suc z) ![c,x,y,k])))
    (hg : Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![y,u]))) :
    Nonempty (Derivation body Gamma (programGraph (guard valid gamma) (suc z) ![x,u])) := by
  have hvx := typedValid typed valid tag c typ x ht
  have hp' := guardedPositiveRecover (basePositive positive gamma) (baseTyped typed valid) tag window _ hp
  obtain ⟨hexy⟩ := positiveGamma positive gamma a b c x y k hx hy hp'
  obtain ⟨dgu⟩ := guardRecover valid gamma b d y u hy hu hg
  exact guardAccept valid gamma a d x u hx hu hvx
    ⟨Derivation.conjunctionLeft dgu⟩ ⟨trans hexy (Derivation.conjunctionRight dgu)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceGraphSupportProof
