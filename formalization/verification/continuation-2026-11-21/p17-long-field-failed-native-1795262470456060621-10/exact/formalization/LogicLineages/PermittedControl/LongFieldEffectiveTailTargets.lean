module
public import LogicLineages.PermittedControl.FieldComparisonTargets
public import LogicLineages.PermittedControl.ThresholdTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- Literal semantic peeling bound used in the existing LongField proof.
The separate code below, not this ordinal definition, is executable. -/
noncomputable def longFieldPeelBound (B : Nat) (lam mu : NONote) (c : Nat) : Nat :=
  max (max 2 (max (actualOrdinalNorm lam.1.repr)
    (max (actualOrdinalNorm (mu.1.repr + Ordinal.omega0 * (c : Ordinal)))
      (actualOrdinalNorm mu.1.repr))))
    (max (actualOrdinalNorm mu.1.repr + 3) (max 1 B))

/-- Semantic witness for the branch whose first coordinate is smaller. -/
noncomputable def longFieldDistinctBound (B : Nat) : ValueField → ValueField → Nat
  | .iterate _, .iterate _ => 0
  | .iterate m, .entry _ lq mq => longFieldPeelBound B lq mq m
  | .entry a lp mp, .iterate n =>
      max (longFieldPeelBound B lp mp 0) (longFieldPeelBound B lp mp (n - a))
  | .entry a lp mp, .entry b lq mq =>
      let mp' := mp + omegaMultiple (b - a)
      let mq' := mq + omegaMultiple (a - b)
      max (max (longFieldPeelBound B lp mp (b - a)) (longFieldPeelBound B lq mq (a - b)))
        (max (inverseTableTail lp mp' mq' (lq - mq') B)
          (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0))

/-- Semantic witness for fields evaluated at the same raw coordinate. -/
noncomputable def longFieldSameBound (B : Nat) : ValueField → ValueField → Nat
  | .iterate _, .iterate _ => 0
  | .iterate m, .entry _ lq mq => longFieldPeelBound B lq mq (m + 1)
  | .entry _ lp mp, .iterate n => longFieldPeelBound B lp mp (n + 1)
  | .entry a lp mp, .entry b lq mq =>
      let mp' := mp + omegaMultiple (b - a)
      let mq' := mq + omegaMultiple (a - b)
      max (max (longFieldPeelBound B lp mp (b - a)) (longFieldPeelBound B lq mq (a - b)))
        (max (max (gapInputTail lq.1.repr mq'.1.repr lp.1.repr mp'.1.repr 0)
          (gapInputTail lp.1.repr mp'.1.repr lq.1.repr mq'.1.repr 0))
          (equalGapCertificateTailCode (rawNoteEncode mp'.1) (rawNoteEncode mq'.1)
            (rawNoteEncode (lp - mp').1) B))

/-- Tag, exponent, raw code of upper endpoint, raw code of lower endpoint.
Zero tag means iterate; any nonzero tag is processed as entry. Calibration
is asserted below only on codes made by `longFieldCode`. -/
abbrev LongFieldCode := Nat × Nat × Nat × Nat

def longFieldCode : ValueField → LongFieldCode
  | .iterate a => (0,a,0,0)
  | .entry a lam mu => (1,a,rawNoteEncode lam.1,rawNoteEncode mu.1)

def omegaMultipleTailCode (c : Nat) : Nat :=
  if c = 0 then 0 else ordinalNodeCode (rawNoteEncode (NONote.ofNat 1).1) (c - 1) 0

def longFieldPeelBoundCode (B lam mu c : Nat) : Nat :=
  max (max 2 (max (rawNormCode lam)
    (max (rawNormCode (ordinalAddCode mu (omegaMultipleTailCode c))) (rawNormCode mu))))
    (max (rawNormCode mu + 3) (max 1 B))

def longFieldDistinctBoundCode (B : Nat) (P Q : LongFieldCode) : Nat :=
  let (tagP,a,lp,mp) := P
  let (tagQ,b,lq,mq) := Q
  if tagP = 0 then
    if tagQ = 0 then 0 else longFieldPeelBoundCode B lq mq a
  else if tagQ = 0 then
    max (longFieldPeelBoundCode B lp mp 0) (longFieldPeelBoundCode B lp mp (b - a))
  else
    let mp' := ordinalAddCode mp (omegaMultipleTailCode (b - a))
    let mq' := ordinalAddCode mq (omegaMultipleTailCode (a - b))
    max (max (longFieldPeelBoundCode B lp mp (b - a)) (longFieldPeelBoundCode B lq mq (a - b)))
      (max (inverseTableTailCode lp mp' mq' (ordinalSubCode lq mq') B)
        (encodedGapInputTail (lq,mq',lp,mp',0)))

def longFieldSameBoundCode (B : Nat) (P Q : LongFieldCode) : Nat :=
  let (tagP,a,lp,mp) := P
  let (tagQ,b,lq,mq) := Q
  if tagP = 0 then
    if tagQ = 0 then 0 else longFieldPeelBoundCode B lq mq (a + 1)
  else if tagQ = 0 then
    longFieldPeelBoundCode B lp mp (b + 1)
  else
    let mp' := ordinalAddCode mp (omegaMultipleTailCode (b - a))
    let mq' := ordinalAddCode mq (omegaMultipleTailCode (a - b))
    max (max (longFieldPeelBoundCode B lp mp (b - a)) (longFieldPeelBoundCode B lq mq (a - b)))
      (max (max (encodedGapInputTail (lq,mq',lp,mp',0)) (encodedGapInputTail (lp,mp',lq,mq',0)))
        (equalGapCertificateTailCode mp' mq' (ordinalSubCode lp mp') B))

/-- Explicit effective tails, calibrated as bounds on the same syntax.
This does not yet require a raw code for the output comparison form. -/
def LongFieldTailEffective : Prop :=
  Primrec omegaMultipleTailCode ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => longFieldPeelBoundCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × LongFieldCode × LongFieldCode => longFieldDistinctBoundCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × LongFieldCode × LongFieldCode => longFieldSameBoundCode p.1 p.2.1 p.2.2) ∧
  (∀ c : Nat, omegaMultipleTailCode c = rawNoteEncode (omegaMultiple c).1) ∧
  (∀ (B : Nat) (lam mu : NONote) (c : Nat),
    longFieldPeelBoundCode B (rawNoteEncode lam.1) (rawNoteEncode mu.1) c =
      longFieldPeelBound B lam mu c) ∧
  ∀ (B : Nat) (F G : ValueField),
    longFieldDistinctBoundCode B (longFieldCode F) (longFieldCode G) = longFieldDistinctBound B F G ∧
    longFieldSameBoundCode B (longFieldCode F) (longFieldCode G) = longFieldSameBound B F G

def LongFieldDistinctAtBound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, LongField F → LongField G →
  ∀ x y : Nat, longFieldDistinctBound B F G ≤ x → x < y →
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G y vG ∧
      FormHolds f (distinctForm F G) x y vF vG

def LongFieldSameAtBound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, LongField F → LongField G →
  ∀ x : Nat, longFieldSameBound B F G ≤ x →
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G x vG ∧
      numericalComparison vF vG = sameForm F G

/-- Supporting on-tail bounds only. Not all-order comparison, finite strips,
or the Paper 17 arithmetic theorem. -/
def FullLongFieldEffectiveTail : Prop :=
  LongFieldTailEffective ∧ LongFieldDistinctAtBound ∧ LongFieldSameAtBound

end LogicLineages.PermittedControl.FieldComparison
