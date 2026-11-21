module
public import LogicLineages.PermittedControl.RawFieldComparisonFormTargets
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- Literal 712 command on the 714/716 field tuple. Iterates stay exactly
unchanged; an entry is retained unless the command emits an iterate. -/
def normalizeHighFieldCode (P : LongFieldCode) : LongFieldCode :=
  let (tag,a,lam,mu) := P
  if tag = 0 then P else
    match shortIterateCode lam mu a with
    | 0 => P
    | n + 1 => (0,n,0,0)

def highShortBoundCode (B : Nat) (P : LongFieldCode) : Nat :=
  let (tag,_,lam,mu) := P
  if tag = 0 then 0 else shortFieldTailCode lam mu B

/-- One uniform bound for both original fields and all three order
branches. Distinct tails always follow their actual argument orientation. -/
def highFieldComparisonBoundCode (B : Nat) (P Q : LongFieldCode) : Nat :=
  let P' := normalizeHighFieldCode P
  let Q' := normalizeHighFieldCode Q
  max (max (highShortBoundCode B P) (highShortBoundCode B Q))
    (max (longFieldSameBoundCode B P' Q')
      (max (longFieldDistinctBoundCode B P' Q') (longFieldDistinctBoundCode B Q' P')))

noncomputable def highFieldComparisonBound (B : Nat) (F G : ValueField) : Nat :=
  let F' := normalizeShortField F
  let G' := normalizeShortField G
  max (max (shortFieldTail B F) (shortFieldTail B G))
    (max (longFieldSameBound B F' G')
      (max (longFieldDistinctBound B F' G') (longFieldDistinctBound B G' F')))

/-- Tag zero is forward; tag one means the result on the sorted arguments
must be reversed to recover the original field order. -/
abbrev OrientedHighFormCode := Nat × RawComparisonFormCode

def flipHighComparisonAnswer (orientation c : Nat) : Nat :=
  if orientation = 0 then c else reverseComparisonCode c

def highRawComparisonForm (P Q : LongFieldCode) (x y : Nat) : OrientedHighFormCode :=
  let P' := normalizeHighFieldCode P
  let Q' := normalizeHighFieldCode Q
  if x < y then (0,rawDistinctForm P' Q')
  else if y < x then (1,rawDistinctForm Q' P')
  else (0,rawConstForm (rawSameForm P' Q'))

def HighFieldComparisonEffective : Prop :=
  Primrec normalizeHighFieldCode ∧
  Primrec₂ highShortBoundCode ∧
  Primrec (fun p : Nat × LongFieldCode × LongFieldCode =>
    highFieldComparisonBoundCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ flipHighComparisonAnswer ∧
  Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat =>
    highRawComparisonForm p.1 p.2.1 p.2.2.1 p.2.2.2)

def HighFieldComparisonCalibration : Prop :=
  (∀ F : ValueField, normalizeHighFieldCode (longFieldCode F) = longFieldCode (normalizeShortField F)) ∧
  (∀ (B : Nat) (F : ValueField), highShortBoundCode B (longFieldCode F) = shortFieldTail B F) ∧
  (∀ (B : Nat) (F G : ValueField),
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) = highFieldComparisonBound B F G) ∧
  ∀ (F G : ValueField) (x y : Nat),
    let F' := normalizeShortField F
    let G' := normalizeShortField G
    let R := highRawComparisonForm (longFieldCode F) (longFieldCode G) x y
    (x < y → R = (0,encodeComparisonForm (distinctForm F' G'))) ∧
    (x = y → R = (0,rawConstForm (sameForm F' G'))) ∧
    (y < x → R = (1,encodeComparisonForm (distinctForm G' F')))

/-- The checked form is linear only through the greater raw coordinate.
The nonlinear field, if selected, is the exact field encoded by the raw
normalizer and evaluated at the smaller coordinate; its properness and
the row sign range are retained. -/
def RawSortedFormHolds (f : Nat → Nat) (R : RawComparisonFormCode)
    (lo hi vLo vHi : Nat) : Prop :=
  (∃ c : Nat, R = rawConstForm c ∧ numericalComparison vLo vHi = c) ∨
  ∃ (sign : Nat) (H : ValueField) (h : Nat),
    R = rawLinearForm sign (longFieldCode H) ∧ sign ≤ 2 ∧ ProperField H ∧
    FieldValue f H lo h ∧ InverseTableRows sign hi h vHi vLo

/-- All three order branches at the actual executable common bound, on
proper original inputs. Values remain those of the original fields at
the original coordinates, including shared coordinates. No claim below
the bound and no replacement by independently assigned parameters. -/
def HighFieldComparisonActual : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, ProperField F → ProperField G →
  ∀ x y : Nat,
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ min x y →
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G y vG ∧
      (∀ u v : Nat, FieldValue f F x u → FieldValue f G y v → u = vF ∧ v = vG) ∧
      let R := highRawComparisonForm (longFieldCode F) (longFieldCode G) x y
      (x < y → R.1 = 0 ∧ RawSortedFormHolds f R.2 x y vF vG) ∧
      (x = y → R = (0,rawConstForm (numericalComparison vF vG))) ∧
      (y < x → R.1 = 1 ∧ RawSortedFormHolds f R.2 y x vG vF ∧
        flipHighComparisonAnswer R.1 (numericalComparison vG vF) = numericalComparison vF vG)

/-- Narrow all-large comparison supplier; not the finite strip calculus,
whole printed field comparison, or arithmetic projection. -/
def FullHighFieldComparison : Prop :=
  HighFieldComparisonEffective ∧ HighFieldComparisonCalibration ∧ HighFieldComparisonActual

end LogicLineages.PermittedControl.FieldComparison
