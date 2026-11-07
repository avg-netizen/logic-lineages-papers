module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open PositiveArithmeticPredicateSubstitution InternalCalculus SourceEndpoint TaggedArithmeticOperators
open JointGammaInvariant InternalSliceInduction SourceComputabilityFormulaSupportProof
open InternalSliceInductionSyntaxProof InternalInvariantSelectionProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof InternalDerivationRenamingProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalSourceIntroductionProof

/-- Transport through every constructor of the unchanged positive grammar.
The selected invariant may itself contain arbitrary negative predicates. -/
theorem tagReplacementSelection (body : Positive (Fin 1)) (odd : Bool)
    {α : Type} (p : Positive α) :
    ∀ (scalar multiset : Formula (α ⊕ Fin 1)),
    Nonempty (Derivation body []
      ((substitutePredicate (tagPredicate odd p) (tagged scalar multiset)).imp
        (substitutePredicate p (pick odd scalar multiset)))) := by
  induction p with
  | arithmetic phi =>
    intro scalar multiset
    exact ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩
  | @predicate α t =>
    intro scalar multiset
    obtain ⟨⟨hs⟩,⟨hm⟩⟩ := actualInternalInvariantSelection body α scalar multiset t
    cases odd with
    | false => exact ⟨Derivation.conjunctionLeft hs⟩
    | true => exact ⟨Derivation.conjunctionLeft hm⟩
  | conj p q ihp ihq =>
    intro scalar multiset
    obtain ⟨dp⟩ := ihp scalar multiset
    obtain ⟨dq⟩ := ihq scalar multiset
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have h : Derivation body
        [substitutePredicate (tagPredicate odd (.conj p q)) (tagged scalar multiset)]
        (substitutePredicate (tagPredicate odd (.conj p q)) (tagged scalar multiset)) :=
      Derivation.hypothesis List.mem_cons_self
    exact Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (weakenClosed dp _) (Derivation.conjunctionLeft h))
      (Derivation.implicationElimination (weakenClosed dq _) (Derivation.conjunctionRight h))
  | guarded guard p ih =>
    intro scalar multiset
    obtain ⟨d⟩ := ih scalar multiset
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    apply Derivation.implicationIntroduction
    let B := arithmeticEmbedding.onFormula guard
    let A := substitutePredicate (tagPredicate odd p) (tagged scalar multiset)
    have hg : Derivation body [B,B.imp A] B := Derivation.hypothesis List.mem_cons_self
    have ha : Derivation body [B,B.imp A] (B.imp A) :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact Derivation.implicationElimination (weakenClosed d _)
      (Derivation.implicationElimination ha hg)
  | @all α p ih =>
    intro scalar multiset
    change Nonempty (Derivation body []
      ((allOne (substitutePredicate (tagPredicate odd p)
        (liftPredicateFormula (tagged scalar multiset)))).imp
        (allOne (substitutePredicate p (liftPredicateFormula (pick odd scalar multiset))))))
    rw [liftTagged,liftPick]
    exact actualInternalUniversalTransport body α _ _
      (ih (liftPredicateFormula scalar) (liftPredicateFormula multiset))

theorem selectedReplacement (body : Positive (Fin 1)) (p : Positive (Fin 2))
    (context : Nat) (odd : Bool) {α : Type} (scalar multiset : Formula (α ⊕ Fin 1)) :
    Nonempty (Derivation body []
      ((replacedBody (specialize (tagPredicate odd p) context) (tagged scalar multiset)).imp
        (replacedBody (specialize p context) (pick odd scalar multiset)))) := by
  change Nonempty (Derivation body []
    ((substitutePredicate (bodyWithParameters (specialize (tagPredicate odd p) context) α)
      (liftPredicateFormula (tagged scalar multiset))).imp
      (substitutePredicate (bodyWithParameters (specialize p context) α)
        (liftPredicateFormula (pick odd scalar multiset)))))
  rw [specializedTagBody,liftTagged,liftPick]
  exact tagReplacementSelection body odd (bodyWithParameters (specialize p context) α)
    (liftPredicateFormula scalar) (liftPredicateFormula multiset)

def precompose {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    {p q r : Formula α} (d : Derivation body Gamma (q.imp r))
    (e : Derivation body [] (p.imp q)) : Derivation body Gamma (p.imp r) := by
  apply Derivation.implicationIntroduction
  exact Derivation.implicationElimination
    (Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) d)
    (Derivation.implicationElimination (weakenClosed e _)
      (Derivation.hypothesis List.mem_cons_self))

/-- A fresh-variable instance uses only derivation renaming and the existing
universal-elimination rule. -/
theorem universalFresh {body : Positive (Fin 1)} {α : Type}
    {Gamma : List (Formula α)} {phi : Formula (α ⊕ Fin 1)}
    (h : Nonempty (Derivation body Gamma (allOne phi))) :
    Nonempty (Derivation body (Gamma.map weaken) phi) := by
  obtain ⟨h⟩ := h
  obtain ⟨d⟩ := renameDerivation h (α ⊕ Fin 1) Sum.inl
  rw [actualUniversalRenaming] at d
  have e := Derivation.universalElimination (.var (.inr 0)) d
  change Derivation body (Gamma.map weaken)
    (instantiate (liftPredicateFormula phi) (.var (.inr (0 : Fin 1)))) at e
  rw [actualFreshInstantiation] at e
  exact ⟨e⟩

/-- The same parameter context is retained while the invariant object is
bound by the original tag guard. -/
theorem branchTransport {body : Positive (Fin 1)} {α : Type}
    (Gamma : List (Formula α)) (odd : Bool) (phi psi : Formula (α ⊕ Fin 1))
    (h : Nonempty (Derivation body (Gamma.map weaken) (phi.imp psi))) :
    Nonempty (Derivation body (Gamma.map weaken) ((branch odd phi).imp (branch odd psi))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := renameDerivation h ((α ⊕ Fin 1) ⊕ Fin 1) (Sum.map Sum.inl id)
  rw [contextWeakenRename] at hs
  change Derivation body ((Gamma.map weaken).map weaken)
    ((liftPredicateFormula phi).imp (liftPredicateFormula psi)) at hs
  let guard : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    eqn (.var (.inl (.inr (0 : Fin 1)))) (tagTerm odd (.var (.inr (0 : Fin 1))))
  have hphi : branch odd phi = allOne (guard.imp (liftPredicateFormula phi)) := by
    rw [branch,onEquality]
    rfl
  have hpsi : branch odd psi = allOne (guard.imp (liftPredicateFormula psi)) := by
    rw [branch,onEquality]
    rfl
  have hb : Derivation body (branch odd phi :: Gamma.map weaken)
      (allOne (guard.imp (liftPredicateFormula phi))) := by
    have hh : Derivation body (branch odd phi :: Gamma.map weaken) (branch odd phi) :=
      Derivation.hypothesis List.mem_cons_self
    simpa only [hphi] using hh
  obtain ⟨hf⟩ := universalFresh ⟨hb⟩
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  rw [hpsi]
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let Delta : List (Formula ((α ⊕ Fin 1) ⊕ Fin 1)) :=
    guard :: (branch odd phi :: Gamma.map weaken).map weaken
  have hp : Derivation body Delta (liftPredicateFormula phi) :=
    Derivation.implicationElimination
      (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) hf)
      (Derivation.hypothesis List.mem_cons_self)
  have hstep : Derivation body Delta
      ((liftPredicateFormula phi).imp (liftPredicateFormula psi)) :=
    Derivation.weakening
      (fun _ hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)) hs
  exact Derivation.implicationElimination hstep hp

/-- The unselected invariant is closed by the original I/J equation in the
same calculus. No closure obligation is delegated to the caller. -/
theorem currentClosure (data : SourcePresentation.Data) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (odd : Bool) :
    Nonempty (Derivation (SourcePresentation.sourceBody data context)
      (replacedBody (sliceBody data context odd) (currentSlice odd) :: Gamma.map weaken)
      (currentSlice odd)) := by
  cases odd with
  | false =>
    obtain ⟨h⟩ := actualInternalScalarEquation data context (α ⊕ Fin 1)
      (.var (.inr (0 : Fin 1)))
    change Nonempty (Derivation (SourcePresentation.sourceBody data context)
      (replacedBody (specialize (SourcePresentation.scalarOperator data) context)
        (currentSlice false) :: Gamma.map weaken) (currentSlice false))
    rw [specializedCurrentReplacement]
    exact ⟨Derivation.implicationElimination (weakenClosed (Derivation.conjunctionRight h) _)
      (Derivation.hypothesis List.mem_cons_self)⟩
  | true =>
    obtain ⟨h⟩ := actualInternalMultisetEquation data context (α ⊕ Fin 1)
      (.var (.inr (0 : Fin 1)))
    change Nonempty (Derivation (SourcePresentation.sourceBody data context)
      (replacedBody (specialize (SourcePresentation.multisetOperator data) context)
        (currentSlice true) :: Gamma.map weaken) (currentSlice true))
    rw [specializedCurrentReplacement]
    exact ⟨Derivation.implicationElimination (weakenClosed (Derivation.conjunctionRight h) _)
      (Derivation.hypothesis List.mem_cons_self)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSupportProof
