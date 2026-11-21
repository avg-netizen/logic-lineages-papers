module
public import LogicLineages.PermittedControl.InverseTableDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- The normal-form notation of `ω`. -/
def omegaNote : NONote :=
  ⟨ONote.omega, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩

/-- The normal-form notation of `ω · c`. -/
def omegaMultiple (c : Nat) : NONote := omegaNote * NONote.ofNat c

/-- Syntax of an ordinary value field in one raw coordinate `u`.
`iterate a` is `f^a(u)`; `iterate 0` is the bare coordinate.
`entry a λ μ` is `f^a(E_{λ,μ}(u))`. -/
inductive ValueField where
  | iterate (a : Nat)
  | entry (a : Nat) (lam mu : NONote)

/-- Actual value of a field at the input `u`: iterates of the control, and
the norm at the genuine first entry of the actual descent. -/
def FieldValue (f : Nat → Nat) : ValueField → Nat → Nat → Prop
  | .iterate a, u, v => v = f^[a] u
  | .entry a lam mu, u, v => ∃ i : Nat,
      FirstEntry f (countInitial lam.1.repr u) mu.1.repr i ∧
      v = f^[a] (entryNormAt f (countInitial lam.1.repr u) i)

/-- Entry fields carry a proper interval. -/
def ProperField : ValueField → Prop
  | .iterate _ => True
  | .entry _ lam mu => Order.IsSuccLimit lam.1.repr ∧
      (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) ∧ mu.1.repr < lam.1.repr

/-- Entry fields carry a proper interval that is not a short interval
`μ + ω k`. A short entry is the bare iterate `f^k(u)` (`ShortEntryIterate`). -/
def LongField : ValueField → Prop
  | .iterate _ => True
  | .entry _ lam mu => Order.IsSuccLimit lam.1.repr ∧
      (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) ∧ mu.1.repr < lam.1.repr ∧
      ¬ ∃ k : Nat, 0 < k ∧ lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal)

/-- A finite Boolean form for the comparison of a field at the smaller
coordinate `x` with a field at the greater coordinate `y`: a fixed answer
(`0` less, `1` equal, `2` greater), or the table row `sign` comparing `y`
itself with the parameter field `H` read at `x`. -/
inductive ComparisonForm where
  | const (c : Nat)
  | linear (sign : Nat) (H : ValueField)

/-- The form of `F(x)` against `G(y)` on the order branch `x < y`. Common
applications of `f` are cancelled and the remaining iterate is peeled off
the opposite entry by advancing its endpoint. -/
def distinctForm : ValueField → ValueField → ComparisonForm
  | .iterate m, .iterate n => if m ≤ n then .const 0 else .linear 1 (.iterate (m - n))
  | .iterate _, .entry _ _ _ => .const 0
  | .entry a lp mp, .iterate n =>
      if n ≤ a then .linear 1 (.entry (a - n) lp mp)
      else .linear 1 (.entry 0 lp (mp + omegaMultiple (n - a)))
  | .entry a lp mp, .entry b lq mq =>
      let mp' := mp + omegaMultiple (b - a)
      let mq' := mq + omegaMultiple (a - b)
      let dp := lp - mp'
      let dq := lq - mq'
      match NONote.cmp dq dp with
      | .lt => .linear (equalGapCertificateCode (rawNoteEncode mp'.1) (rawNoteEncode mq'.1)
          (rawNoteEncode dq.1)) (.entry 0 lp (mp' + dq))
      | _ => .const 0

/-- The fixed answer for two fields read at the same coordinate. -/
def sameForm : ValueField → ValueField → Nat
  | .iterate m, .iterate n => numericalComparison m n
  | .iterate _, .entry _ _ _ => 0
  | .entry _ _ _, .iterate _ => 2
  | .entry a lp mp, .entry b lq mq =>
      let mp' := mp + omegaMultiple (b - a)
      let mq' := mq + omegaMultiple (a - b)
      let dp := lp - mp'
      let dq := lq - mq'
      match NONote.cmp dp dq with
      | .lt => 0
      | .gt => 2
      | .eq => equalGapCertificateCode (rawNoteEncode mp'.1) (rawNoteEncode mq'.1)
          (rawNoteEncode dp.1)

/-- Meaning of a form for the actual values `vF` of the field at `x` and
`vG` of the field at `y`. In the linear case `y` occurs only in the
comparisons `y < h`, `y = h`, `h < y` (and their unit shifts) with the
value `h` of a field at `x`. -/
def FormHolds (f : Nat → Nat) : ComparisonForm → Nat → Nat → Nat → Nat → Prop
  | .const c, _, _, vF, vG => numericalComparison vF vG = c
  | .linear sign H, x, y, vF, vG => ∃ h : Nat, FieldValue f H x h ∧ InverseTableRows sign y h vG vF

/-- A short entry is a bare iterate, with its constant count. -/
def ShortEntryIterate : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu : Ordinal.{0}) (k x : Nat), 0 < k → mu + Ordinal.omega0 * (k : Ordinal) < epsilonZero →
    (mu = 0 ∨ Order.IsSuccLimit mu) →
    max (actualOrdinalNorm (mu + Ordinal.omega0 * (k : Ordinal)))
      (max (actualOrdinalNorm mu + 3) (max 1 B)) ≤ x →
    FirstEntry f (countInitial (mu + Ordinal.omega0 * (k : Ordinal)) x) mu k ∧
    entryNormAt f (countInitial (mu + Ordinal.omega0 * (k : Ordinal)) x) k = f^[k] x

/-- A field has at most one value at an input. -/
def FieldValueUnique : Prop := ∀ (f : Nat → Nat) (F : ValueField) (u v v' : Nat),
  FieldValue f F u v → FieldValue f F u v' → v = v'

/-- Every linear form uses a table sign and a proper parameter field. -/
def FormWellFormed : Prop := ∀ F G : ValueField, LongField F → LongField G →
  ∀ (sign : Nat) (H : ValueField), distinctForm F G = .linear sign H → sign ≤ 2 ∧ ProperField H

/-- On the order branch `x < y`, beyond a tail depending only on the two
fields and the control, both fields have actual values and their
comparison is the computed form. -/
def DistinctInputForm : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, LongField F → LongField G →
  ∃ T : Nat, ∀ x y : Nat, T ≤ x → x < y →
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G y vG ∧
      FormHolds f (distinctForm F G) x y vF vG

/-- On the branch where the two coordinates are identified, the comparison
is the computed fixed answer. -/
def EqualInputForm : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, LongField F → LongField G →
  ∃ T : Nat, ∀ x : Nat, T ≤ x →
    ∃ vF vG : Nat, FieldValue f F x vF ∧ FieldValue f G x vG ∧
      numericalComparison vF vG = sameForm F G

/-- Current17 `lem:field-comparison`. -/
def FullFieldComparison : Prop :=
  ShortEntryIterate ∧ FieldValueUnique ∧ FormWellFormed ∧ DistinctInputForm ∧ EqualInputForm

end LogicLineages.PermittedControl.FieldComparison
