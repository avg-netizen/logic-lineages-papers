module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphZeroEliminationProof
open InternalRecursionGraphSuccessorEliminationProof InternalRecursionGraphZeroIntroductionProof
open InternalGraphCompositionSyntaxProof InternalGraphCompositionEqualityProof InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalBetaDivisionSyntaxProof InternalBetaTotalitySyntaxProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalAdditionLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def prefixForward (a b c d n i r : OrdinaryArithmetic.Term α)
    (h : Derivation body Gamma (InternalBetaExtension.sameBelow a b c d n))
    (hi : Derivation body Gamma (ltF i n)) (hb : Derivation body Gamma (beta a b i r)) :
    Derivation body Gamma (beta c d i r) :=
  Derivation.implicationElimination (Derivation.conjunctionLeft
    (InternalBetaExtensionConsumerProof.sameBelowElim a b c d n i r h hi)) hb

def prefixBackward (a b c d n i r : OrdinaryArithmetic.Term α)
    (h : Derivation body Gamma (InternalBetaExtension.sameBelow a b c d n))
    (hi : Derivation body Gamma (ltF i n)) (hb : Derivation body Gamma (beta c d i r)) :
    Derivation body Gamma (beta a b i r) :=
  Derivation.implicationElimination (Derivation.conjunctionRight
    (InternalBetaExtensionConsumerProof.sameBelowElim a b c d n i r h hi)) hb

theorem betaUnique (a b i r s : OrdinaryArithmetic.Term α)
    (hr : Nonempty (Derivation body Gamma (beta a b i r)))
    (hs : Nonempty (Derivation body Gamma (beta a b i s))) :
    Nonempty (Derivation body Gamma (eqn r s)) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  obtain ⟨unique⟩ := InternalBetaUniquenessProof.actualOriginalBetaUniqueness body α a b i r s
  rw [onEquality] at unique
  exact ⟨Derivation.implicationElimination (weakenClosed unique Gamma)
    (Derivation.conjunctionIntroduction hr hs)⟩

theorem betaIndexTransport (a b i j r : OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation body Gamma (eqn i j)))
    (hb : Nonempty (Derivation body Gamma (beta a b i r))) :
    Nonempty (Derivation body Gamma (beta a b j r)) := by
  obtain ⟨he⟩ := he
  obtain ⟨hb⟩ := hb
  let theta := beta (a.relabel Sum.inl) (b.relabel Sum.inl)
    (.var (.inr (0 : Fin 1))) (r.relabel Sum.inl)
  have hi : Derivation body Gamma (instantiate theta (emb i)) := by
    simp only [theta,beta,betaInstantiate,liftBind,varBind]
    exact hb
  have hj := Derivation.equalityElimination theta (emb i) (emb j) he hi
  simp only [theta,beta,betaInstantiate,liftBind,varBind] at hj
  exact ⟨hj⟩

/-- The additive order witness remains unchanged when both endpoints increase. -/
theorem successorOrder (s t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (suc s) (suc t))) := by
  apply orderCases Gamma s t _ h
  intro β j Delta w _ ⟨e⟩
  simp only [orderRename,sucRelabel]
  apply actualOriginalOrderIntroduction body β Delta (suc (s.relabel j)) (suc (t.relabel j)) w
  rw [onEquality]
  exact ⟨trans (leftSuccessor (s.relabel j) (suc w)) (congSuc e)⟩

/-- Prefix equivalence transfers the original universally guarded base test. -/
theorem initialTransfer {n : Nat} (Gamma : List (Formula α)) (f : OFormula (Fin (n+1)))
    (a b c d t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hi : Nonempty (Derivation body Gamma (initial f a b xs)))
    (hp : Nonempty (Derivation body Gamma (InternalBetaExtension.sameBelow a b c d (suc t)))) :
    Nonempty (Derivation body Gamma (initial f c d xs)) := by
  unfold initial OrdinaryArithmetic.initialGraph
  rw [actualOriginalUniversalEmbedding]
  apply actualFiniteUniversalIntroduction body α 1 Gamma
  let v : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 1)
  let C := c.relabel (Sum.inl : α → α ⊕ Fin 1)
  let D := d.relabel (Sum.inl : α → α ⊕ Fin 1)
  let T := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let P := beta C D z v
  let Delta := P :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 1))
  have hi' := renameInto hi Sum.inl Delta (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [initialRename] at hi'
  have hp' := renameInto hp Sum.inl Delta (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [InternalBetaExtensionSyntaxProof.sameBelowRename,sucRelabel] at hp'
  obtain ⟨hp'⟩ := hp'
  have hb : Nonempty (Derivation body Delta (beta A B z v)) :=
    ⟨prefixBackward A B C D (suc T) z v hp' (zeroLessSuccessor T)
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨res⟩ := initialElimination Delta f A B v (fun i => (xs i).relabel Sum.inl) hi' hb
  exact ⟨Derivation.implicationIntroduction res⟩

/-- An old interior step is preserved through both required prefix positions. -/
theorem oldStepBranch {n : Nat} (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (a b c d t j v w : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma (step g a b t xs)))
    (hp : Nonempty (Derivation body Gamma (InternalBetaExtension.sameBelow a b c d (suc t))))
    (hj : Nonempty (Derivation body Gamma (ltF j t)))
    (hv : Nonempty (Derivation body Gamma (beta c d j v)))
    (hw : Nonempty (Derivation body Gamma (beta c d (suc j) w))) :
    Nonempty (Derivation body Gamma (graph g w (Fin.cons j (Fin.cons v xs)))) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hv⟩ := hv
  obtain ⟨hw⟩ := hw
  obtain ⟨hnext⟩ := successorOrder j t hj
  obtain ⟨hj'⟩ := hj
  obtain ⟨ord⟩ := actualRightSuccessorOrder body α j t
  have hjn := Derivation.implicationElimination (weakenClosed ord Gamma) hj'
  exact stepElimination Gamma g a b t j v w xs hs ⟨hj'⟩
    ⟨prefixBackward a b c d (suc t) j v hp hjn hv⟩
    ⟨prefixBackward a b c d (suc t) (suc j) w hp hnext hw⟩

/-- The boundary step follows from beta uniqueness and equality transport,
without any functionality assumption on the arithmetic graph g. -/
theorem boundaryStepBranch {n : Nat} (Gamma : List (Formula α)) (g : OFormula (Fin (n+3)))
    (c d out t old j v w : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hold : Nonempty (Derivation body Gamma (beta c d t old)))
    (hend : Nonempty (Derivation body Gamma (beta c d (suc t) out)))
    (hg : Nonempty (Derivation body Gamma (graph g out (Fin.cons t (Fin.cons old xs)))))
    (he : Nonempty (Derivation body Gamma (eqn j t)))
    (hv : Nonempty (Derivation body Gamma (beta c d j v)))
    (hw : Nonempty (Derivation body Gamma (beta c d (suc j) w))) :
    Nonempty (Derivation body Gamma (graph g w (Fin.cons j (Fin.cons v xs)))) := by
  have hv' := betaIndexTransport c d j t v he hv
  obtain ⟨he⟩ := he
  have hw' := betaIndexTransport c d (suc j) (suc t) w ⟨congSuc he⟩ hw
  have hprev := betaUnique c d t old v hold hv'
  have hnext := betaUnique c d (suc t) out w hend hw'
  obtain ⟨hprev⟩ := hprev
  let source : Fin (n+2) → OrdinaryArithmetic.Term α := Fin.cons t (Fin.cons old xs)
  let target : Fin (n+2) → OrdinaryArithmetic.Term α := Fin.cons j (Fin.cons v xs)
  have hcoords : ∀ i : Fin (n+2), Nonempty (Derivation body Gamma
      (arithmeticEmbedding.onFormula ((source i).equal (target i)))) := by
    intro i
    rw [onEquality]
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) i
    · exact ⟨symm he⟩
    · exact ⟨hprev⟩
    · exact ⟨refl (xs l)⟩
  have input := graphInputTransport body α (n+2) Gamma g out
    (Fin.cons t (Fin.cons old xs)) (Fin.cons j (Fin.cons v xs)) hcoords hg
  exact graphOutputTransport Gamma g out w (Fin.cons j (Fin.cons v xs)) hnext input
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
