module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
public import LogicLineages.PermittedControl.ConcreteCountPairReplacementTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement
open ConcreteCountPairReplacement
open SelectedCountOnlyClass (prefixTarget)

structure SurvivingPrefix where
  rank : Nat
  lam : NONote
  eta : NONote
  weight : Int
  count : Nat

def SurvivingPrefix.asRead (p : SurvivingPrefix) : Read :=
  ((p.weight,.count p.rank p.lam p.eta),p.count)

noncomputable def SurvivingPrefix.key (f : Nat → Nat) (ρ : Nat → Nat) (p : SurvivingPrefix) : Nat :=
  f (entryNormAt f (countInitial p.lam.1.repr (ρ p.rank)) p.count)

def ActualPrefix (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (p : SurvivingPrefix) : Prop :=
  p.weight ≠ 0 ∧ 0 < p.count ∧ shortGapLength p.lam p.eta = 0 ∧
    liftedReads f ρ [p.asRead] ∧ p.key f ρ = C

/-- The cohort comprises exactly the selected count prefixes still
present after the literal zero-class replacement. Match the original
fold's order, retain duplicates, and use each actual unchanged rank. -/
noncomputable def survivingPrefix (f : Nat → Nat) (C : Nat) (t : WeightedOperand) :
    Annotation → Option SurvivingPrefix
  | .count i q _ =>
      match t.2 with
      | .count rank lam mu =>
          let eta := prefixTarget mu
          if f q = C ∧ i ≠ 0 ∧ shortGapLength lam eta = 0 then
            some ⟨rank,lam,eta,t.1,i⟩
          else none
      | _ => none
  | _ => none

noncomputable def cohort (f : Nat → Nat) (C : Nat) :
    List WeightedOperand → List Annotation → List SurvivingPrefix
  | t::terms,ann::annotations =>
      (survivingPrefix f C t ann).toList ++ cohort f C terms annotations
  | _,_ => []

def ExactCohort : Prop :=
  (∀ (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat)
    (ann : Annotation) (p : SurvivingPrefix),
    LowerOperandActual f ρ t.2 v → ActualAnnotation f ρ t v ann →
    survivingPrefix f C t ann = some p →
    ActualPrefix f ρ C p ∧ (replaceOccurrence f C t v ann).1 = some p.asRead) ∧
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations →
    ∀ p ∈ cohort f C terms annotations, ActualPrefix f ρ C p

/-- The least rank yields the smallest surviving raw input in the fixed
strict order. Ties keep the first original occurrence. -/
def leastPrefix : List SurvivingPrefix → Option SurvivingPrefix
  | [] => none
  | p::ps =>
      match leastPrefix ps with
      | none => some p
      | some q => if p.rank ≤ q.rank then some p else some q

def ExactLeastPrefix : Prop :=
  (∀ ps : List SurvivingPrefix, leastPrefix ps = none ↔ ps = []) ∧
  ∀ (ps : List SurvivingPrefix) (anchor : SurvivingPrefix),
    leastPrefix ps = some anchor → anchor ∈ ps ∧ ∀ p ∈ ps, anchor.rank ≤ p.rank

def pairTail (B : Nat) (anchor p : SurvivingPrefix) : Nat :=
  safeTailCode (intervalPairCodes p.lam p.eta anchor.lam anchor.eta) B

def TransferReady (B : Nat) (ρ : Nat → Nat) (ps : List SurvivingPrefix) : Prop :=
  ∀ anchor, leastPrefix ps = some anchor → ∀ p ∈ ps, anchor.rank < p.rank →
    pairTail B anchor p ≤ ρ anchor.rank ∧ pairTail B anchor p ≤ ρ p.rank

def anchorRead (anchor : SurvivingPrefix) (weight : Int) : Read :=
  ((weight,.count anchor.rank anchor.lam anchor.eta),anchor.count)

noncomputable def subtractRead (anchor p : SurvivingPrefix) (i : Nat) : Read :=
  ((-p.weight,replacementOperand anchor.rank p.lam p.eta anchor.lam anchor.eta),i)

/-- Each source occurrence contributes the one chosen lower prefix at
its original signed weight. A genuine higher collision additionally
subtracts the original H count at that same lower rank. -/
inductive MovedPrefixes (f : Nat → Nat) (ρ : Nat → Nat) (anchor : SurvivingPrefix) :
    List SurvivingPrefix → List Read → Prop
  | nil : MovedPrefixes f ρ anchor [] []
  | same {p ps out} :
      p.rank = anchor.rank → p.count = anchor.count →
      MovedPrefixes f ρ anchor ps out →
      MovedPrefixes f ρ anchor (p::ps) (anchorRead anchor p.weight :: out)
  | higher {p ps out i} :
      anchor.rank < p.rank → anchor.count = i + p.count →
      entryNormAt f (countInitial anchor.lam.1.repr (ρ anchor.rank)) i = ρ p.rank →
      MovedPrefixes f ρ anchor ps out →
      MovedPrefixes f ρ anchor (p::ps)
        (anchorRead anchor p.weight :: subtractRead anchor p i :: out)

def ExactCohortTransfer : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C : Nat) (terms : List WeightedOperand) (values : List Nat)
    (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations →
    let ps := cohort f C terms annotations
    TransferReady B ρ ps →
    match leastPrefix ps with
    | none => ps = []
    | some anchor =>
        anchor ∈ ps ∧ (∀ p ∈ ps, anchor.rank ≤ p.rank) ∧
        ∃ out, MovedPrefixes f ρ anchor ps out ∧ liftedReads f ρ out ∧
          readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
          ∀ read ∈ out, read.1.2.rank = anchor.rank

def FullActualZeroClassCohortTransfer : Prop :=
  ExactCohort ∧ ExactLeastPrefix ∧ ExactCohortTransfer

end LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
