module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The literal candidate query of the frozen `observed` guard. -/
abbrev candidateQuery (O : Program 1) : Program 3 :=
  Program.composition O (fun _ : Fin 1 => (Program.projection 1 : Program 3))

/-- The literal seed query of the frozen `observed` guard. -/
abbrev seedQuery (O : Program 1) : Program 3 :=
  Program.composition O (fun _ : Fin 1 => (Program.projection 0 : Program 3))

/-- Accepted literal equality test: a known left value is the right value.
The unknown right output comes from internal Program totality. -/
theorem sameKnownLeft {n : Nat} (p q : Program n) (value : OTerm α) (xs : Fin n → OTerm α)
    (he : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma (programGraph q value xs)) := by
  apply programCases q xs _
  intro β j Delta right hj hr
  simp only [programRename]
  have he' := renameInto he j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at he' hp'
  obtain ⟨hEq⟩ := InternalEqualityTestProof.equalityOfAcceptance (value.relabel j) right
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) (value.relabel j) right
      (fun i => (xs i).relabel j) he' hp' hr)
  exact outputTransport q right (value.relabel j) (fun i => (xs i).relabel j) ⟨symm hEq⟩ hr

/-- Accepted literal equality test: a known right value is the left value. -/
theorem sameKnownRight {n : Nat} (p q : Program n) (value : OTerm α) (xs : Fin n → OTerm α)
    (he : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q value xs))) :
    Nonempty (Derivation body Gamma (programGraph p value xs)) := by
  apply programCases p xs _
  intro β j Delta left hj hl
  simp only [programRename]
  have he' := renameInto he j Delta hj
  have hq' := renameInto hq j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at he' hq'
  have hEq := InternalEqualityTestProof.equalityOfAcceptance left (value.relabel j)
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) left (value.relabel j)
      (fun i => (xs i).relabel j) he' hl hq')
  exact outputTransport p left (value.relabel j) (fun i => (xs i).relabel j) hEq hl

/-- Reflexive branch: an internal equality of candidate and seed transports
the observer graph in both directions. No class hit is used. -/
theorem observerOfEqual (O : Program 1) (mark out seed : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out seed))) :
    Nonempty (Derivation body Gamma ((graph1 O mark out).iff (graph1 O mark seed))) := by
  obtain ⟨he⟩ := he
  obtain ⟨hf⟩ := headTransport (n := 0) (body := body) (Gamma := graph1 O mark out :: Gamma)
    O mark out seed Fin.elim0 ⟨addHyp he _⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := headTransport (n := 0) (body := body) (Gamma := graph1 O mark seed :: Gamma)
    O mark seed out Fin.elim0 ⟨addHyp (symm he) _⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- Nonreflexive branch: the explicit `same` conjunct of `observed` yields
observer equality at every mark. -/
theorem observerOfSame (O : Program 1) (mark seed out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same (candidateQuery O) (seedQuery O)) (suc z)
        (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma ((graph1 O mark out).iff (graph1 O mark seed))) := by
  let xs : Fin 3 → OTerm α := Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0))
  obtain ⟨hs⟩ := hs
  have hf : Nonempty (Derivation body (graph1 O mark out :: Gamma) (graph1 O mark seed)) := by
    have hl := unaryValue (body := body) (Gamma := graph1 O mark out :: Gamma)
      O (.projection 1) mark out xs ⟨Derivation.hypothesis List.mem_cons_self⟩
      (projectionValue 1 xs)
    have hr := sameKnownLeft (body := body) (Gamma := graph1 O mark out :: Gamma)
      (candidateQuery O) (seedQuery O) mark xs ⟨addHyp hs _⟩ hl
    exact unaryRecover O (.projection 0) mark seed xs hr (projectionValue 0 xs)
  have hb : Nonempty (Derivation body (graph1 O mark seed :: Gamma) (graph1 O mark out)) := by
    have hr := unaryValue (body := body) (Gamma := graph1 O mark seed :: Gamma)
      O (.projection 0) mark seed xs ⟨Derivation.hypothesis List.mem_cons_self⟩
      (projectionValue 0 xs)
    have hl := sameKnownRight (body := body) (Gamma := graph1 O mark seed :: Gamma)
      (candidateQuery O) (seedQuery O) mark xs ⟨addHyp hs _⟩ hr
    exact unaryRecover O (.projection 1) mark out xs hl (projectionValue 1 xs)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- A rejected actual equality control selects the guarded class branch of the
literal `reflexiveClassTest`; its conjunction exposes the `same` guard. -/
theorem observerOfRejected (T : Program 2) (O : Program 1) (P : Program 3)
    (mark seed out parameter : OTerm α)
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z out seed)))
    (hw : Nonempty (Derivation body Gamma
      (programGraph (OriginalTransparentMinimum.reflexiveClassTest T
        (OriginalObservedClass.observed O P)) (suc z)
        (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma ((graph1 O mark out).iff (graph1 O mark seed))) := by
  let xs : Fin 3 → OTerm α := Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0))
  have hc : Nonempty (Derivation body Gamma
      (programGraph (Program.composition InternalEqualityTest.equalityTest
        ![(Program.projection 1 : Program 3),Program.projection 0]) z xs)) :=
    binaryValue InternalEqualityTest.equalityTest (.projection 1) (.projection 0) z out seed xs
      hz (projectionValue 1 xs) (projectionValue 0 xs)
  have ho : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.conjunction P
        (InternalApplicationStepPeel.same (candidateQuery O) (seedQuery O))) (suc z) xs)) :=
    zeroBranchElim
      (Program.composition InternalEqualityTest.equalityTest
        ![(Program.projection 1 : Program 3),Program.projection 0])
      (InternalAcceptance.conjunction P
        (InternalApplicationStepPeel.same (candidateQuery O) (seedQuery O)))
      (Program.composition T ![(Program.projection 0 : Program 3),Program.projection 2])
      (suc z) xs hc hw
  exact observerOfSame O mark seed out parameter
    (andRight (conjunctionRecover P
      (InternalApplicationStepPeel.same (candidateQuery O) (seedQuery O)) xs ho))

/-- Internal trichotomy on candidate and seed. The equal case is the actual
reflexive control; both strict cases reject the control and use the guard. -/
theorem observedHit (T : Program 2) (O : Program 1) (P : Program 3)
    (seed out parameter mark : OTerm α) :
    Nonempty (Derivation body Gamma
      ((programGraph (OriginalTransparentMinimum.reflexiveClassTest T
          (OriginalObservedClass.observed O P)) (suc z)
          (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))).imp
        ((graph1 O mark out).iff (graph1 O mark seed)))) := by
  let A : Formula α := programGraph (OriginalTransparentMinimum.reflexiveClassTest T
    (OriginalObservedClass.observed O P)) (suc z)
    (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))
  have hw : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨cmp⟩ := actualOriginalComparison body α out seed
  have hc := compareView (weakenClosed cmp (A :: Gamma))
  obtain ⟨hl⟩ := observerOfRejected (body := body) (Gamma := ltF out seed :: A :: Gamma)
    T O P mark seed out parameter
    (InternalEqualityTestProof.rejectForwardOrder out seed
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hw _⟩
  obtain ⟨he⟩ := observerOfEqual (body := body) (Gamma := eqn out seed :: A :: Gamma)
    O mark out seed ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := observerOfRejected (body := body) (Gamma := ltF seed out :: A :: Gamma)
    T O P mark seed out parameter
    (InternalEqualityTestProof.rejectBackwardOrder out seed
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hw _⟩
  have rest : Derivation body (A :: Gamma)
      ((eqn out seed ⊔ ltF seed out).imp ((graph1 O mark out).iff (graph1 O mark seed))) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination hc (Derivation.implicationIntroduction hl) rest)⟩

theorem actualOriginalObservedClassHit :
    OriginalObservedClassTargets.ActualOriginalObservedClassHit := by
  intro T O P body alpha Delta seed out parameter mark
  exact observedHit T O P seed out parameter mark

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassProof
