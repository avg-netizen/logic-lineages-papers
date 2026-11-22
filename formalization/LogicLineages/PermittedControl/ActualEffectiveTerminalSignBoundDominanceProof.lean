module
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets
import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundCalibrationProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
open PreparedProjection MixedSameRankResidue ActualMixedRowLeadingSum
open ActualZeroClassCommonTail ActualZeroEdgeAlphabet ActualZeroEdgeConstantShift
open ActualReadChargeIteration ActualFiniteGlobalTail ActualTraceSignCutoff
open ActualSignedReadMass ActualShortCountCleanup ActualSyntaxChargeBudget

private theorem finiteMaxMember {α : Type} (cost : α → Nat) (items : List α) (x : α)
    (member : x ∈ items) : cost x ≤ finiteMax cost items := by
  induction items with
  | nil => cases member
  | cons a rest ih =>
      change cost x ≤ max (cost a) (finiteMax cost rest)
      rcases List.mem_cons.mp member with eq | later
      · subst x
        exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

private theorem finiteMaxMono {α : Type} (cost : α → Nat) (left right : List α)
    (sub : ∀ x ∈ left, x ∈ right) : finiteMax cost left ≤ finiteMax cost right := by
  induction left with
  | nil => exact Nat.zero_le _
  | cons a tail ih =>
      change max (cost a) (finiteMax cost tail) ≤ finiteMax cost right
      exact max_le (finiteMaxMember cost right a (sub a List.mem_cons_self))
        (ih (fun x hx => sub x (List.mem_cons_of_mem _ hx)))

private theorem prefixesMono (left right : List LowerOperand)
    (sub : ∀ x ∈ left, x ∈ right) :
    ∀ p ∈ prefixCandidates left, p ∈ prefixCandidates right := by
  intro p member
  obtain ⟨key,source,equal⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr ⟨key,sub key source,equal⟩

private theorem expandMono (left right : List LowerOperand)
    (sub : ∀ x ∈ left, x ∈ right) :
    ∀ op ∈ expand left, op ∈ expand right := by
  intro op member
  have keep := prefixesMono left right sub
  rcases List.mem_append.mp member with orig | extra
  · exact List.mem_append.mpr (Or.inl (sub op orig))
  · apply List.mem_append.mpr
    right
    rcases List.mem_append.mp extra with prefixHit | pairs
    · apply List.mem_append.mpr
      left
      obtain ⟨l,lMem,shown⟩ := List.mem_map.mp prefixHit
      exact List.mem_map.mpr ⟨l,keep l lMem,shown⟩
    · apply List.mem_append.mpr
      right
      obtain ⟨lo,loMem,row⟩ := List.mem_flatMap.mp pairs
      obtain ⟨hi,hiMem,shown⟩ := List.mem_map.mp row
      obtain ⟨higher,ordered⟩ := List.mem_filter.mp hiMem
      exact List.mem_flatMap.mpr ⟨lo,keep lo loMem,List.mem_map.mpr
        ⟨hi,List.mem_filter.mpr ⟨keep hi higher,ordered⟩,shown⟩⟩

private theorem factorsMono (left right : List LowerOperand) (sub : ∀ op ∈ left, op ∈ right) :
    correctionMaximum left ≤ correctionMaximum right ∧ edgeFactor left ≤ edgeFactor right := by
  have corr := finiteMaxMono correctionBound left right sub
  have pre := finiteMaxMono (fun l : PrefixLabel => FieldComparison.shortGapLength l.lam l.eta)
    (prefixCandidates left) (prefixCandidates right) (prefixesMono left right sub)
  have clean := finiteMaxMono shortLength (expand left) (expand right) (expandMono left right sub)
  exact ⟨corr,Nat.add_le_add (Nat.add_le_add corr pre) (Nat.mul_le_mul_left 3 clean)⟩

private theorem alphabetDepthMono (terms : List WeightedOperand) {small large : Nat} (bound : small ≤ large) :
    ∀ op ∈ depthAlphabet small terms, op ∈ depthAlphabet large terms := by
  intro op member
  obtain ⟨d,inside,atDepth⟩ := List.mem_flatMap.mp member
  have depth : d < small+1 := List.mem_range.mp inside
  exact List.mem_flatMap.mpr ⟨d,List.mem_range.mpr (depth.trans_le (Nat.succ_le_succ bound)),atDepth⟩

theorem signCeilingMono (c : Int) (terms : List WeightedOperand) {small large : Nat} (bound : small ≤ large) :
    signCeilingAtBudget small c terms ≤ signCeilingAtBudget large c terms := by
  let a := depthAlphabet small terms
  let b := depthAlphabet large terms
  let u := 3 ^ small * syntaxMass terms
  let v := 3 ^ large * syntaxMass terms
  have mass : u ≤ v :=
    Nat.mul_le_mul_right (syntaxMass terms) (Nat.pow_le_pow_right (by decide) bound)
  obtain ⟨corr,factor⟩ := factorsMono a b (alphabetDepthMono terms bound)
  have constants : c.natAbs + small * (u * edgeFactor a) ≤ c.natAbs + large * (v * edgeFactor b) :=
    Nat.add_le_add_left (Nat.mul_le_mul bound (Nat.mul_le_mul mass factor)) _
  change SelectedLeadingSignCutoff.cutoff (2*u) ((c.natAbs + small * (u * edgeFactor a)) +
      u * correctionMaximum a) ≤ SelectedLeadingSignCutoff.cutoff (2*v)
      ((c.natAbs + large * (v * edgeFactor b)) + v * correctionMaximum b)
  unfold SelectedLeadingSignCutoff.cutoff
  exact Nat.mul_le_mul_left 4 (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 2 mass)
      (Nat.add_le_add constants (Nat.mul_le_mul mass corr))) 2)

private theorem inputMassLiteral (reads : List ActualZeroClassReplacement.Read) :
    syntaxMass (reads.map Prod.fst) = signedMass reads := by
  induction reads with
  | nil => rfl
  | cons rd reads ih =>
      change rd.1.1.natAbs + syntaxMass (reads.map Prod.fst) =
        rd.1.1.natAbs + signedMass reads
      rw [ih]

private theorem exactBudgetLiteral (r : Nat) (s : ReadState) :
    signCeilingAtBudget (syntaxCharge r (syntaxOf s)) s.constant (syntaxOf s) =
      terminalCutoffCeiling r s := by
  have mass : syntaxMass (syntaxOf s) = signedMass s.reads := inputMassLiteral s.reads
  unfold signCeilingAtBudget terminalCutoffCeiling constantCeiling stepCeiling massCeiling globalAlphabet depthAlphabet
  rw [mass]

theorem exactSignBoundDominance : ExactSignBoundDominance := by
  intro r initial
  rw [inputLiteral r initial.constant (syntaxOf initial),← exactBudgetLiteral r initial]
  exact signCeilingMono initial.constant (syntaxOf initial)
    (exactChargeBudget.2.1 r (syntaxOf initial))

end LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
