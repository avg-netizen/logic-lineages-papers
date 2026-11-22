module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets
import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyPairNarrowProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferCohortProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsOrbitProof
import LogicLineages.PermittedControl.GapInputFoundationProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ConcreteCountPairReplacement

private theorem prefixOrbit (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (p : SurvivingPrefix)
    (actual : LowerOperandActual f ρ p.asRead.1.2 p.count) :
    entryNormAt f (countInitial p.lam.1.repr (ρ p.rank)) p.count = f^[p.count] (ρ p.rank) := by
  obtain ⟨⟨lamLimit,etaLimit,below⟩,affordable⟩ := actual.1
  exact (SelectedNonlinearImageBounds.actualPrefixErrorBound f B selected p.lam p.eta
    (ρ p.rank) p.count lamLimit etaLimit below.le affordable actual.2).1

private theorem assemblyAppendMovedPrefix (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (ordered : StrictMono ρ) (C : Nat) (anchor p : SurvivingPrefix)
    (anchorPrefix : ActualPrefix f ρ C anchor) (sourcePrefix : ActualPrefix f ρ C p)
    (least : anchor.rank ≤ p.rank)
    (funded : anchor.rank < p.rank →
      pairTail B anchor p ≤ ρ anchor.rank ∧ pairTail B anchor p ≤ ρ p.rank)
    (ps : List SurvivingPrefix) (out : List Read)
    (moved : MovedPrefixes f ρ anchor ps out) (outputReads : liftedReads f ρ out)
    (value : readSum (ps.map SurvivingPrefix.asRead) = readSum out)
    (atRank : ∀ read ∈ out, read.1.2.rank = anchor.rank) :
    ∃ next, MovedPrefixes f ρ anchor (p::ps) next ∧ liftedReads f ρ next ∧
      readSum ((p::ps).map SurvivingPrefix.asRead) = readSum next ∧
      ∀ read ∈ next, read.1.2.rank = anchor.rank := by
  obtain ⟨_,_,_,anchorReads,anchorKey⟩ := anchorPrefix
  obtain ⟨_,_,_,sourceReads,sourceKey⟩ := sourcePrefix
  obtain ⟨anchorActual,anchorEncoded,_⟩ := anchorReads
  obtain ⟨sourceActual,_,_⟩ := sourceReads
  have keys : f (entryNormAt f (countInitial p.lam.1.repr (ρ p.rank)) p.count) =
      f (entryNormAt f (countInitial anchor.lam.1.repr (ρ anchor.rank)) anchor.count) :=
    sourceKey.trans anchorKey.symm
  rcases least.eq_or_lt with equal | higher
  · have norms := (selected_threshold_admissible f B selected).1.injective keys
    change entryNormAt f (countInitial p.lam.1.repr (ρ p.rank)) p.count =
      entryNormAt f (countInitial anchor.lam.1.repr (ρ anchor.rank)) anchor.count at norms
    rw [prefixOrbit f B selected ρ p sourceActual,
      prefixOrbit f B selected ρ anchor anchorActual,← equal] at norms
    have same := (selected_iterate_strict f B selected (ρ anchor.rank)).injective norms
    refine ⟨anchorRead anchor p.weight :: out,.same equal.symm same moved,
      ⟨anchorActual,anchorEncoded,outputReads⟩,?_,?_⟩
    · change p.weight * (p.count : Int) + readSum (ps.map SurvivingPrefix.asRead) =
        p.weight * (anchor.count : Int) + readSum out
      rw [same,value]
    · intro read member
      rcases List.mem_cons.mp member with eq | tail
      · subst read
        rfl
      · exact atRank read tail
  · obtain ⟨atLower,atHigher⟩ := funded higher
    obtain ⟨_,_,_,_,rankH,i,_,middle,_,count,signed,domainH,actualH,_⟩ :=
      assemblyActualPairReplacement f B selected p.lam p.eta
        anchor.lam anchor.eta sourceActual.1.1 anchorActual.1.1 ρ anchor.rank p.rank
        anchor.count p.count atLower atHigher (ordered higher) anchorActual.2 sourceActual.2 keys
    have encodedH := (((closedOrdinaryCountActual f anchor.lam
      (anchor.eta + (p.lam - p.eta)) (ρ anchor.rank)).2 domainH).1 i).mpr actualH.2
    refine ⟨anchorRead anchor p.weight :: subtractRead anchor p i :: out,
      .higher higher count middle moved,⟨anchorActual,anchorEncoded,actualH,encodedH,outputReads⟩,
      ?_,?_⟩
    · have weighted : p.weight * (p.count : Int) =
          p.weight * (anchor.count : Int) + (-p.weight) * (i : Int) := by
        rw [signed,mul_sub,neg_mul,sub_eq_add_neg]
      change p.weight * (p.count : Int) + readSum (ps.map SurvivingPrefix.asRead) =
        p.weight * (anchor.count : Int) + ((-p.weight) * (i : Int) + readSum out)
      rw [weighted,value,add_assoc]
    · intro read member
      rcases List.mem_cons.mp member with eq | rest
      · subst read
        rfl
      rcases List.mem_cons.mp rest with eq | tail
      · subst read
        exact rankH
      · exact atRank read tail

private theorem transferToAnchor (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (ordered : StrictMono ρ) (C : Nat) (anchor : SurvivingPrefix)
    (anchorActual : ActualPrefix f ρ C anchor) (ps : List SurvivingPrefix)
    (actual : ∀ p ∈ ps, ActualPrefix f ρ C p)
    (least : ∀ p ∈ ps, anchor.rank ≤ p.rank)
    (paid : ∀ p ∈ ps, anchor.rank < p.rank →
      pairTail B anchor p ≤ ρ anchor.rank ∧ pairTail B anchor p ≤ ρ p.rank) :
    ∃ out, MovedPrefixes f ρ anchor ps out ∧ liftedReads f ρ out ∧
      readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
      ∀ read ∈ out, read.1.2.rank = anchor.rank := by
  induction ps with
  | nil => exact ⟨[],.nil,True.intro,rfl,fun read member => False.elim (List.not_mem_nil member)⟩
  | cons p ps next =>
      obtain ⟨out,moved,reads,value,rank⟩ :=
        next (fun q member => actual q (List.mem_cons_of_mem _ member))
          (fun q member => least q (List.mem_cons_of_mem _ member))
          (fun q member => paid q (List.mem_cons_of_mem _ member))
      exact assemblyAppendMovedPrefix f B selected ρ ordered C anchor p anchorActual
        (actual p List.mem_cons_self) (least p List.mem_cons_self) (paid p List.mem_cons_self)
        ps out moved reads value rank

theorem assemblyCohortTransfer : ExactCohortTransfer := by
  intro f B selected ρ ordered C terms values annotations aligned
  dsimp only
  intro ready
  let ps := cohort f C terms annotations
  have actual : ∀ p ∈ ps, ActualPrefix f ρ C p :=
    exactCohort.2 f ρ C terms values annotations aligned
  change TransferReady B ρ ps at ready
  change match leastPrefix ps with
    | none => ps = []
    | some anchor =>
        anchor ∈ ps ∧ (∀ p ∈ ps, anchor.rank ≤ p.rank) ∧
        ∃ out, MovedPrefixes f ρ anchor ps out ∧ liftedReads f ρ out ∧
          readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
          ∀ read ∈ out, read.1.2.rank = anchor.rank
  cases found : leastPrefix ps with
  | none => exact (exactLeastPrefix.1 ps).mp found
  | some anchor =>
      obtain ⟨member,least⟩ := exactLeastPrefix.2 ps anchor found
      exact ⟨member,least,transferToAnchor f B selected ρ ordered C anchor
        (actual anchor member) ps actual least (ready anchor found)⟩

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
