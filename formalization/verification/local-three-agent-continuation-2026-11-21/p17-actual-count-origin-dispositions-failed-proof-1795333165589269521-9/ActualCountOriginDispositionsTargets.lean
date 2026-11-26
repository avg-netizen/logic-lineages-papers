module
public import LogicLineages.PermittedControl.ActualRankedZeroClassTargets
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountOriginDispositions
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open ActualRankedZeroClass
open SelectedCountOnlyClass (prefixTarget)

abbrev Origin := Read × Annotation
abbrev CountDisposition := InnerTerminationTargets.Disposition (NONote × NONote)

def isCountAnnotation : Annotation → Bool
  | .count _ _ _ => true
  | _ => false

def countOrigins (f : Nat → Nat) (C : Nat) (xs : List Read)
    (annotations : List Annotation) : List Origin :=
  (classLedger f C xs annotations).filter (fun entry => isCountAnnotation entry.2)

noncomputable def originSurvivors (f : Nat → Nat) (C : Nat) (origins : List Origin) :
    List SurvivingPrefix :=
  origins.filterMap (fun entry => survivingPrefix f C entry.1.1 entry.2)

def OriginPaid (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (entry : Origin) : Prop :=
  LowerOperandActual f ρ entry.1.1.2 entry.1.2 ∧
    lowerOperandRead f ρ entry.1.1.2 = some (some entry.1.2) ∧
    ActualAnnotation f ρ entry.1.1 entry.1.2 entry.2 ∧ fullValue f entry.2 = some C ∧
    PrefixTailReady f B ρ C entry.1.1 entry.2 ∧ isCountAnnotation entry.2 = true

def ExactCountOrigins : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (xs : List Read) (annotations : List Annotation),
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    Ready f B ρ C (xs.map Prod.fst) annotations →
    let origins := countOrigins f C xs annotations
    (∀ entry ∈ origins, OriginPaid f B ρ C entry) ∧
    originSurvivors f C origins = cohort f C (xs.map Prod.fst) annotations

/-- The source label remains (λ, μ) here, even when distinct original μ
have equal prefix target notes after adding ω². Every shift is per unit
weight in the actual source's existing finite-charge disposition type. -/
def OriginOutcome (f : Nat → Nat) (ρ : Nat → Nat) (selectedAnchor : Option SurvivingPrefix)
    (entry : Origin) (d : CountDisposition) (out : List Read) : Prop :=
  liftedReads f ρ out ∧
  match entry.1.1.2,entry.2 with
  | .count rank lam mu,.count i _ κ =>
      let eta := prefixTarget mu
      let k := shortGapLength lam eta
      if i = 0 then
        eta.1.repr = lam.1.repr ∧ d = .ended κ ∧ out = []
      else if k = 0 then
        ∃ anchor, selectedAnchor = some anchor ∧
          LowerOperandActual f ρ (.count rank lam eta) i ∧
          lowerOperandRead f ρ (.count rank lam eta) = some (some i) ∧
          if rank = anchor.rank then
            i = anchor.count ∧ d = .survives κ ∧ out = [anchorRead anchor entry.1.1.1]
          else
            anchor.rank < rank ∧ ∃ h : Nat,
              anchor.count = h + i ∧
              entryNormAt f (countInitial anchor.lam.1.repr (ρ anchor.rank)) h = ρ rank ∧
              d = .transferred (some (anchor.lam,anchor.eta + (lam - eta))) κ ∧
              out = [anchorRead anchor entry.1.1.1,
                subtractRead anchor ⟨rank,lam,eta,entry.1.1.1,i⟩ h]
      else i = k ∧ d = .ended (κ + (k : Int)) ∧ out = []
  | _,_ => False

inductive DisposedOrigins (f : Nat → Nat) (ρ : Nat → Nat) (anchor : Option SurvivingPrefix) :
    List Origin → List (Origin × CountDisposition) → List Read → Prop
  | nil : DisposedOrigins f ρ anchor [] [] []
  | cons {entry entries d ledger first tail} :
      OriginOutcome f ρ anchor entry d first →
      DisposedOrigins f ρ anchor entries ledger tail →
      DisposedOrigins f ρ anchor (entry::entries) ((entry,d)::ledger) (first ++ tail)

def MovedAt (f : Nat → Nat) (ρ : Nat → Nat) : Option SurvivingPrefix →
    List SurvivingPrefix → List Read → Prop
  | none,ps,out => ps = [] ∧ out = []
  | some anchor,ps,out => MovedPrefixes f ρ anchor ps out

def ExactOriginDispositions : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C : Nat) (xs : List Read) (annotations : List Annotation),
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    Ready f B ρ C (xs.map Prod.fst) annotations →
    let ps := cohort f C (xs.map Prod.fst) annotations
    ∀ (anchor : Option SurvivingPrefix) (out : List Read),
      anchor = leastPrefix ps → MovedAt f ρ anchor ps out → liftedReads f ρ out →
      ∃ ledger, DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger out

def FullActualCountOriginDispositions : Prop := ExactCountOrigins ∧ ExactOriginDispositions

end LogicLineages.PermittedControl.ActualCountOriginDispositions
