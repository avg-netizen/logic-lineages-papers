module
public import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassTargets
public import LogicLineages.PermittedControl.ActualCountCoreLabelsTargets
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroSuccessorMarkedClass (Marked actualMarked)
open SelectedCountOnlyClass (prefixTarget)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations CountTailReady)
open ActualZeroClassCohortTransfer (SurvivingPrefix cohort leastPrefix)

inductive CountPlan where
  | invalid
  | identity
  | short (target : NONote) (k : Nat)
  | survives (target : NONote)

/-- Original selected long count only. Its prefix, not the original
count interval, can newly be short after the removal. -/
def countPlan (lam mu : NONote) : CountPlan :=
  match ActualCountCoreLabels.classify lam mu with
  | .identityPrefix => .identity
  | .properPrefix eta =>
      let k := shortGapLength lam eta
      if k = 0 then .survives eta else .short eta k
  | _ => .invalid

structure PrefixSyntax where
  rank : Nat
  lam : NONote
  eta : NONote
  weight : Int

def erase (p : SurvivingPrefix) : PrefixSyntax := ⟨p.rank,p.lam,p.eta,p.weight⟩

def markedPrefix (m : Marked) : Option PrefixSyntax :=
  if m.2 then
    match m.1.2 with
    | .count rank lam mu =>
        match countPlan lam mu with
        | .survives eta => some ⟨rank,lam,eta,m.1.1⟩
        | _ => none
    | _ => none
  else none

def cohortSyntax (marked : List Marked) : List PrefixSyntax := marked.filterMap markedPrefix

/-- Literal least-rank fold with the same original first tie. -/
def leastSyntax : List PrefixSyntax → Option PrefixSyntax
  | [] => none
  | p::ps =>
      match leastSyntax ps with
      | none => some p
      | some q => if p.rank ≤ q.rank then some p else some q

def strictPrefixRead (f ρ : Nat → Nat) (rank : Nat) (lam eta : NONote) (i : Nat) : Prop :=
  0 < i ∧ LowerOperandActual f ρ (.count rank lam eta) i ∧
    lowerOperandRead f ρ (.count rank lam eta) = some (some i)

noncomputable def shortPrefixTail (B : Nat) (lam eta : NONote) : Nat :=
  max (actualOrdinalNorm lam.1.repr)
    (max (actualOrdinalNorm eta.1.repr + 3) (max 1 B))

def PlanFacts (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat)
    (rank : Nat) (lam mu : NONote) (i : Nat) : CountPlan → Prop
  | .invalid => False
  | .identity => i = 0 ∧ (prefixTarget mu).1.repr = lam.1.repr
  | .short eta k => eta = prefixTarget mu ∧ shortGapLength lam (prefixTarget mu) = k ∧
      0 < k ∧ strictPrefixRead f ρ rank lam eta i ∧
        (shortPrefixTail B lam eta ≤ ρ rank → i = k)
  | .survives eta => eta = prefixTarget mu ∧ shortGapLength lam (prefixTarget mu) = 0 ∧
      strictPrefixRead f ρ rank lam eta i

def ExactCountPrefixPlan : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote) (v i : Nat),
    LongField (.entry 0 lam mu) →
    max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3) ≤ ρ rank →
    LowerOperandActual f ρ (.count rank lam mu) v →
    FirstEntry f (countInitial lam.1.repr (ρ rank)) (prefixTarget mu).1.repr i →
      PlanFacts f B ρ rank lam mu i (countPlan lam mu)

def ExactCanonicalPrefixAnchor : Prop :=
  ∀ ps : List SurvivingPrefix,
    leastSyntax (ps.map erase) = (leastPrefix ps).map erase

def ExactSelectedCohortSyntax : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand)
    (values : List Nat) (anns : List Annotation),
    AlignedAnnotations f ρ terms values anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
      cohortSyntax (actualMarked f C terms anns) = (cohort f C terms anns).map erase ∧
      leastSyntax (cohortSyntax (actualMarked f C terms anns)) =
        (leastPrefix (cohort f C terms anns)).map erase

def FullActualZeroSuccessorPrefixPlan : Prop :=
  ExactCountPrefixPlan ∧ ExactCanonicalPrefixAnchor ∧ ExactSelectedCohortSyntax

end LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
