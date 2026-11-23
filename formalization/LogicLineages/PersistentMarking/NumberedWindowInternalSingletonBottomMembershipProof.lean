module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipEmptyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembership
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (equal)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalAccessibilityRulesProof
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalSourceInversionSupportProof (tagSubstitution)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc emb eqn zRelabel bindEmbedding varBind)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTermSubstitutionProof (predicateSubstitution)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.SourcePresentation (Data sourceBody)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalSingletonBottomTargets (packedSingletonBottom)
open NumberedWindowInternalSingletonBottomBranch
  (exactSingletonGuardSelection exactSymbolicSingletonCertificateTarget)
open NumberedWindowInternalEmptyMultiset (exactDirectSelection)
open NumberedWindowInternalEmptyMultisetTargets (emptyGuard)
open NumberedWindowInternalSingletonBottomMembershipEmpty (rejectEmpty)
open NumberedWindowInternalSingletonBottomMembershipTargets
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

private theorem consRename {α β : Type} (h t : OrdinaryArithmetic.Term α) (ρ : α → β) :
    (consTerm h t).relabel ρ = consTerm (h.relabel ρ) (t.relabel ρ) :=
  rawConsRename h t ρ

private theorem singletonRename {α β : Type} (ctx t : OrdinaryArithmetic.Term α) (ρ : α → β) :
    (packedSingletonBottom ctx t).relabel ρ = packedSingletonBottom (ctx.relabel ρ) (t.relabel ρ) := by
  simp only [packedSingletonBottom,rawConsRename,packedBottomTerm,addressTerm,consRename,numeralRename,zRelabel]

private theorem oddEdgeCases {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (S : Data) (c : Nat) (f g : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation B Γ (edge S true c f g)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w : OrdinaryArithmetic.Term β),
      Nonempty (Derivation B Δ (certificate S true c (f.relabel j) (g.relabel j) w)) →
      Nonempty (Derivation B Δ (psi.relabel j))) :
    Nonempty (Derivation B Γ psi) := by
  obtain ⟨h⟩ := h
  rw [edgeExists] at h
  let P := certificate S true c (f.relabel Sum.inl) (g.relabel Sum.inl)
    (.var (.inr (0 : Fin 1)))
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (P :: Γ.map weaken) (.var (.inr 0))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

private theorem successorsOf {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (S : Data) (c : Nat) (x : OrdinaryArithmetic.Term α)
    (next : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (y : OrdinaryArithmetic.Term β),
      Nonempty (Derivation B Δ (edge S true c (x.relabel ρ) y)) →
      Nonempty (Derivation B Δ (membership true y))) :
    Nonempty (Derivation B Γ (successors S true c x)) := by
  let β := α ⊕ Fin 1
  let y : OrdinaryArithmetic.Term β := .var (.inr 0)
  let H := edge S true c (x.relabel Sum.inl) y
  let Δ := H :: Γ.map weaken
  obtain ⟨h⟩ := next β Sum.inl Δ y ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction h)⟩

private theorem instantiateJ {α : Type} (x : OrdinaryArithmetic.Term α) :
    instantiate (membership true (.var (.inr (0 : Fin 1)) : OrdinaryArithmetic.Term (α ⊕ Fin 1))) (emb x) =
      membership true x := by
  unfold instantiate membership
  rw [bindEmbedding,← predicateSubstitution,tagSubstitution,varBind]

private theorem zeroMembershipTransport {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (y : OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation B Γ (equal y z)))
    (hj : Nonempty (Derivation B Γ (membership true (z : OrdinaryArithmetic.Term α)))) :
    Nonempty (Derivation B Γ (membership true y)) := by
  obtain ⟨e⟩ := he
  rw [equalEqn] at e
  obtain ⟨member⟩ := hj
  let G : Formula (α ⊕ Fin 1) := membership true (.var (.inr 0))
  have atZero : Derivation B Γ (instantiate G (emb (z : OrdinaryArithmetic.Term α))) := by
    rw [show instantiate G (emb (z : OrdinaryArithmetic.Term α)) = membership true z from instantiateJ z]
    exact member
  have atY := Derivation.equalityElimination G (emb (z : OrdinaryArithmetic.Term α)) (emb y) (symm e) atZero
  rw [show instantiate G (emb y) = membership true y from instantiateJ y] at atY
  exact ⟨atY⟩

private theorem emptyMembers (i j : Program 1) (r d : Program 3)
    (c : Nat) (α : Type) (Γ : List (Formula α)) (hj : evaluate j (0 ::ᵥ nil) = 1) :
    let S := data i j r (selectedDirect d)
    Nonempty (Derivation (sourceBody S c) Γ (membership true (z : OrdinaryArithmetic.Term α))) := by
  let D := selectedDirect d
  let S := data i j r D
  let B := sourceBody S c
  let a : OrdinaryArithmetic.Term α := z
  change Nonempty (Derivation B Γ (membership true a))
  have graph := exact_NumeralGraph 1 j (0 ::ᵥ nil) B α Γ
  have coords : inputs (α := α) (0 ::ᵥ nil) = ![a] := by
    funext k
    exact Fin.cases rfl (fun p => Fin.elim0 p) k
  rw [hj,coords] at graph
  have carry : Nonempty (Derivation B Γ (carrier S true c a)) :=
    (exact_DomainRules i j r D true c B α Γ a).2 graph
  apply actualOriginalAccessibilityIntroduction S true c α Γ a carry
  apply successorsOf S c a
  intro β ρ Δ y h
  have edge0 : Nonempty (Derivation B Δ (edge S true c (z : OrdinaryArithmetic.Term β) y)) := by
    simpa only [a,zRelabel] using h
  apply oddEdgeCases S c z y (membership true y) edge0
  intro γ k Ω w cert
  have c0 : Nonempty (Derivation B Ω (certificate S true c (z : OrdinaryArithmetic.Term γ)
      (y.relabel k) w)) := by simpa only [zRelabel] using cert
  obtain ⟨bad⟩ := rejectEmpty i j r d c γ Ω (y.relabel k) w c0
  exact ⟨Derivation.explosion bad⟩

private theorem singletonMembers (i j : Program 1) (r d : Program 3)
    (c : Nat) (α : Type) (Γ : List (Formula α)) (ctx t : OrdinaryArithmetic.Term α)
    (hj : evaluate j (0 ::ᵥ nil) = 1) :
    let S := data i j r (selectedDirect d)
    let B := sourceBody S c
    Nonempty (Derivation B Γ (carrier S true c (packedSingletonBottom ctx t))) →
    Nonempty (Derivation B Γ (membership true (packedSingletonBottom ctx t))) := by
  dsimp only
  intro carry
  let D := selectedDirect d
  let S := data i j r D
  let B := sourceBody S c
  apply actualOriginalAccessibilityIntroduction S true c α Γ (packedSingletonBottom ctx t) carry
  apply successorsOf S c (packedSingletonBottom ctx t)
  intro β ρ Δ y h
  let ct := ctx.relabel ρ
  let ty := t.relabel ρ
  have edgeAt : Nonempty (Derivation B Δ (edge S true c (packedSingletonBottom ct ty) y)) := by
    simpa only [singletonRename,ct,ty] using h
  apply oddEdgeCases S c (packedSingletonBottom ct ty) y (membership true y) edgeAt
  intro γ k Ω w cert
  have certAt : Nonempty (Derivation B Ω (certificate S true c
      (packedSingletonBottom (ct.relabel k) (ty.relabel k)) (y.relabel k) w)) := by
    simpa only [singletonRename] using cert
  have zero := exactSymbolicSingletonCertificateTarget i j r (emptyGuard d) c γ Ω
    (ct.relabel k) (ty.relabel k) (y.relabel k) w certAt
  have empty := emptyMembers i j r d c γ Ω hj
  rw [NumberedWindowInternalAtomicMembershipSyntaxProof.membershipRename]
  exact zeroMembershipTransport (y.relabel k) zero empty

theorem exactSelectedSingletonBottomMembership : ExactSelectedSingletonBottomMembership := by
  intro xs s
  obtain ⟨i,j,r,d,old,_,_⟩ :=
    NumberedWindowInternalAccessibilityChecks.exact_ConcreteInternalAccessibility xs s
  let D := selectedDirect d
  let S := data i j r D
  have ev : Evaluates (checks xs s) i j r D :=
    exactSingletonGuardSelection xs s i j r (emptyGuard d) (exactDirectSelection xs s i j r d old)
  refine ⟨i,j,r,d,old,ev,?_,?_,?_⟩
  · exact NumberedWindowFormulaCalibrationChecks.exact_InterpretsEvaluatingPrograms
      (checks xs s) i j r D ev
  · exact ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩
  · intro c α Γ
    have hj : evaluate j (0 ::ᵥ nil) = 1 := ev.2.1 0
    exact ⟨emptyMembers i j r d c α Γ hj,
      fun ctx t => singletonMembers i j r d c α Γ ctx t hj⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembership
