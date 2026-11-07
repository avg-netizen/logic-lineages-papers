module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open InternalEqualityTestPredecessorProof InternalEqualityTestSubtractionSupportProof
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalAdditionLawsProof InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof InternalGraphCompositionFunctionalityProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem diagonalZero : Nonempty (Derivation body Gamma (diagonalRow (z : OTerm α))) := by
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  simp only [zRelabel]
  change Derivation body (Gamma.map weaken) (subGraph y z (add z y))
  exact Classical.choice (subTransport y z y z (add z y) ⟨refl z⟩ ⟨symm (leftZero y)⟩ (subtractZero y))

/-- The object-induction invariant quantifies the entire second argument.
At the successor step the induction hypothesis is instantiated at succ(y). -/
theorem diagonalStep (x : OTerm α)
    (h : Nonempty (Derivation body Gamma (diagonalRow x))) :
    Nonempty (Derivation body Gamma (diagonalRow (suc x))) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  let a := x.relabel (Sum.inl : α → α ⊕ Fin 1)
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  simp only [sucRelabel]
  change Derivation body (Gamma.map weaken) (subGraph y (suc a) (add (suc a) y))
  have hr : Nonempty (Derivation body (Gamma.map weaken) (diagonalRow a)) := by
    have r := InternalOriginalOrderProof.renameInto ⟨h⟩ Sum.inl (Gamma.map weaken)
      (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
    simpa only [diagonalRowRename] using r
  have prev := diagonalElimination a (suc y) hr
  have next := subtractSuccessor y (suc y) a (add a (suc y)) prev (predecessorSuccessor y)
  exact Classical.choice (subTransport y (suc a) (add a (suc y)) (suc a) (add (suc a) y)
    ⟨refl _⟩ ⟨trans (addSucc a y) (symm (leftSuccessor a y))⟩ next)

theorem diagonalAll (x : OTerm α) : Nonempty (Derivation body Gamma (diagonalRow x)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := diagonalRow v
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,v,diagonalRowInstantiate,varBind]
    exact Classical.choice diagonalZero
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,v,successorInstance,nextEmbedding,diagonalRowSubst,varNext]
    exact Classical.choice (diagonalStep v
      (show Nonempty (Derivation body (theta :: Gamma.map weaken) (diagonalRow v)) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have h := Derivation.universalElimination (emb x) (natInduction theta hb hs)
  simpa only [theta,v,diagonalRowInstantiate,varBind] using (Nonempty.intro h)

theorem diagonal (x y : OTerm α) : Nonempty (Derivation body Gamma (subGraph y x (add x y))) :=
  diagonalElimination x y (diagonalAll x)

theorem subtractSelf (x : OTerm α) : Nonempty (Derivation body Gamma (subGraph z x x)) :=
  subTransport z x (add x z) x x ⟨refl x⟩ ⟨addZero x⟩ (diagonal x z)

/-- Once the previous output is zero, the predecessor step fixes zero. -/
theorem absorption (x y : OTerm α) :
    Nonempty (Derivation body Gamma (subGraph z (add x y) x)) := by
  let a := x.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := subGraph z (add a v) a
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,v,subGraphInstantiate,zSubst,addSubst,liftBind,varBind]
    exact Classical.choice (subTransport z x x (add x z) x
      ⟨symm (addZero x)⟩ ⟨refl x⟩ (subtractSelf x))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,v,successorInstance,nextEmbedding,subGraphSubst,zSubst,addSubst,liftNext,varNext]
    have prev : Nonempty (Derivation body (theta :: Gamma.map weaken) (subGraph z (add a v) a)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have next := subtractSuccessor z z (add a v) a prev predecessorZero
    exact Classical.choice (subTransport z (suc (add a v)) a (add a (suc v)) a
      ⟨symm (addSucc a v)⟩ ⟨refl a⟩ next)
  have h := Derivation.universalElimination (emb y) (natInduction theta hb hs)
  simpa only [theta,a,v,subGraphInstantiate,zSubst,addSubst,liftBind,varBind] using (Nonempty.intro h)

theorem actualOriginalSubtractionDiagonal : InternalEqualityTestTargets.ActualOriginalSubtractionDiagonal := by
  intro body α x y
  exact diagonal x y

theorem actualOriginalSubtractionAbsorption : InternalEqualityTestTargets.ActualOriginalSubtractionAbsorption := by
  intro body α x y
  exact absorption x y

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
