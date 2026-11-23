module
public import LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultiset
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalCalculus (weaken)
open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAccessibilityRulesProof
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateTargets (RawDomain)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules exact_CertificateRules)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (chooseBranch zeroAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (branchEvaluation zeroEvaluation)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalEmptyMultisetTargets
open NumberedWindowDirectAlgorithm (directLists readWitness typedList)
open NumberedWindowFieldAlgorithm (unpack)

private theorem directListsAtNil (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (ys : List Nat) (w : NumberedWindowDirectAlgorithm.Witness) :
    directLists scalar positive [] ys w = false := by
  by_cases h : ([] : List Nat).Perm (w.1 ++ w.2.1)
  · have hlen : w.2.1.length = 0 := by
      have he := h.length_eq
      simp only [List.length_nil,List.length_append] at he
      omega
    have hn : w.2.1 = [] := List.eq_nil_of_length_eq_zero hlen
    simp [directLists,hn]
  · simp [directLists,h]

private theorem directAtZero (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool) (w y : Nat) :
    NumberedWindowDirectAlgorithm.direct scalar positive 0 w y = false := by
  have hu : unpack 0 = some [] := rfl
  unfold NumberedWindowDirectAlgorithm.direct
  rw [hu]
  cases h : readWitness w <;> cases hy : unpack y <;>
    simp only [h,hy,directListsAtNil]

private theorem guardedValue (d : Program 3) (x w y : Nat) :
    evaluate (emptyGuard d) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if x = 0 then 0 else evaluate d (x ::ᵥ w ::ᵥ y ::ᵥ nil) := by
  change evaluate (chooseBranch (.projection 0) (zeroAt 3) d) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = _
  rw [branchEvaluation,zeroEvaluation] <;> rfl

theorem exactDirectSelection : ExactDirectSelection := by
  intro xs s i j r d h
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro x w y
  rw [guardedValue]
  by_cases hx : x = 0
  · subst x
    change (if 0 = 0 then 0 else evaluate d (0 ::ᵥ w ::ᵥ y ::ᵥ nil)) =
      (NumberedWindowConcreteCheckers.direct xs s 0 w y).toNat
    unfold NumberedWindowConcreteCheckers.direct NumberedWindowAddressCheckers.direct
    rw [directAtZero] <;> rfl
  · rw [if_neg hx]
    exact h.2.2.2 x w y

private theorem emptyGraph {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d : Program 3) (w y : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (programGraph (emptyGuard d) OrdinaryArithmetic.zeroTerm
      ![OrdinaryArithmetic.zeroTerm,w,y])) := by
  let z : OrdinaryArithmetic.Term α := OrdinaryArithmetic.zeroTerm
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![z,w,y]
  apply zeroBranchIntro (.projection 0) (constantZero 3) d z xs
  · exact projectionValue 0 xs
  · apply ID1Completion.InternalControlGraphSupportProof.compositionValue .zero Fin.elim0 z xs Fin.elim0
    · exact ID1Completion.InternalControlGraphSupportProof.zeroValue Fin.elim0
    · exact fun k => Fin.elim0 k

theorem exactOpenEmptyCertificateRejection : ExactOpenEmptyCertificateRejection := by
  intro i j r d c α Γ y w
  dsimp only
  intro cert
  let S := data i j r (emptyGuard d)
  let B := sourceBody S c
  let z : OrdinaryArithmetic.Term α := OrdinaryArithmetic.zeroTerm
  have accept := (exact_CertificateRules i j r (emptyGuard d) true c B α Γ z y w).1 cert
  change Nonempty (Derivation B Γ (programGraph (emptyGuard d)
    (OrdinaryArithmetic.succTerm z) ![z,w,y])) at accept
  obtain ⟨bad⟩ := valueUnique (emptyGuard d) (OrdinaryArithmetic.succTerm z) z ![z,w,y]
    accept (emptyGraph d w y)
  exact ⟨sucNeZeroApply bad⟩

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

private theorem oddSuccessorsOf {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
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

private theorem emptySuccessors (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) :
    let S := data i j r (emptyGuard d)
    Nonempty (Derivation (sourceBody S c) Γ
      (successors S true c (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term α))) := by
  let S := data i j r (emptyGuard d)
  let B := sourceBody S c
  let z : OrdinaryArithmetic.Term α := OrdinaryArithmetic.zeroTerm
  change Nonempty (Derivation B Γ (successors S true c z))
  apply oddSuccessorsOf S c z
  intro β ρ Δ y h
  have hEdge : Nonempty (Derivation B Δ
      (edge S true c (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term β) y)) := by
    simpa only [z,zRelabel] using h
  apply oddEdgeCases S c OrdinaryArithmetic.zeroTerm y (membership true y) hEdge
  intro γ k Ω w cert
  have hc : Nonempty (Derivation B Ω
      (certificate S true c (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term γ)
        (y.relabel k) w)) := by simpa only [zRelabel] using cert
  obtain ⟨bad⟩ := exactOpenEmptyCertificateRejection i j r d c γ Ω (y.relabel k) w hc
  exact ⟨Derivation.explosion bad⟩

theorem exactSelectedEmptyMultiset : ExactSelectedEmptyMultiset := by
  intro xs s
  obtain ⟨i,j,r,d,old,_,_⟩ :=
    NumberedWindowInternalAccessibilityChecks.exact_ConcreteInternalAccessibility xs s
  let D := emptyGuard d
  let S := data i j r D
  have he := exactDirectSelection xs s i j r d old
  refine ⟨i,j,r,d,old,he,?_,?_,?_⟩
  · exact NumberedWindowFormulaCalibrationChecks.exact_InterpretsEvaluatingPrograms
      (checks xs s) i j r D he
  · exact ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩
  · intro c α Γ
    let B := sourceBody S c
    let z : OrdinaryArithmetic.Term α := OrdinaryArithmetic.zeroTerm
    have hj : evaluate j (0 ::ᵥ nil) = 1 := he.2.1 0
    have h := exact_NumeralGraph 1 j (0 ::ᵥ nil) B α Γ
    have coords : inputs (α := α) (0 ::ᵥ nil) = ![z] := by
      funext k
      exact Fin.cases rfl (fun p => Fin.elim0 p) k
    rw [hj,coords] at h
    have carry : Nonempty (Derivation B Γ (carrier S true c z)) :=
      (exact_DomainRules i j r D true c B α Γ z).2 h
    exact actualOriginalAccessibilityIntroduction S true c α Γ z carry
      (emptySuccessors i j r d c α Γ)

end LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultiset
