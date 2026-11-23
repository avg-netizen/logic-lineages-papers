module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldInvariantProof
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowPositivePathAlgorithm (advance)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathAdvanceTargets (packedOriginalAdvance encodeState decodeState)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpinePositiveRankProof (exact_OriginalNeutralRankAdvance)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)

/-- The original per-hop semantics on exactly the physical packed context and fields. -/
def packedCallback (xs : Entries) (s : Settings) (c ty : Nat) (state : Option Nat) (hop : Nat) :
    Option Nat := packedOriginalAdvance xs s c ty (encodeState state) hop

def retainsZero (q : Nat) : Bool := rawRank q == 0

private theorem packedAbsent (xs : Entries) (s : Settings) (c ty hop : Nat) :
    packedCallback xs s c ty none hop = none := by
  unfold packedCallback packedOriginalAdvance
  cases decoded : unpack c <;> rfl

/-- The actual checked original advance cannot return from positive rank
to rank zero, even when decoded from a packed physical context. -/
theorem exact_PackedCallbackNonzeroPersists (xs : Entries) (s : Settings)
    (c ty src hop dst : Nat) (earlier : rawRank src ≠ 0)
    (hit : packedCallback xs s c ty (some src) hop = some dst) :
    rawRank dst ≠ 0 := by
  cases decoded : unpack c with
  | none =>
    simp only [packedCallback,packedOriginalAdvance,decoded,Option.bind_eq_bind,Option.bind_none] at hit
    cases hit
  | some g =>
    have actual : advance (step xs s g ty) (least s g ty) (some src) hop = some dst := by
      simpa only [packedCallback,packedOriginalAdvance,decoded,Option.bind_eq_bind,Option.bind_some,
        encodeState,decodeState] using hit
    exact (exact_OriginalNeutralRankAdvance xs s (exact_OriginalKeepsNeutralRank s)
      g ty src hop dst earlier actual).1

private theorem filterStep {α β : Type} (keep : α → Bool) (f : Option α → β → Option α)
    (absent : ∀ h, f none h = none)
    (neverReturn : ∀ a h b, keep a = false → f (some a) h = some b → keep b = false)
    (x : Option α) (h : β) :
    (f (x.filter keep) h).filter keep = (f x h).filter keep := by
  cases x with
  | none => rfl
  | some a =>
    cases before : keep a with
    | true =>
      have allow : (some a).filter keep = some a := Option.filter_some_pos before
      rw [allow]
    | false =>
      rw [Option.filter_some_neg before,absent]
      cases next : f (some a) h with
      | none => rfl
      | some b =>
        rw [Option.filter_some_neg (neverReturn a h b before next)] <;> rfl

private theorem filterFold {α β : Type} (keep : α → Bool) (f : Option α → β → Option α)
    (absent : ∀ h, f none h = none)
    (neverReturn : ∀ a h b, keep a = false → f (some a) h = some b → keep b = false) :
    ∀ (hops : List β) (x : Option α),
      hops.foldl (fun state hop => (f state hop).filter keep) (x.filter keep) =
        (hops.foldl f x).filter keep := by
  intro hops
  induction hops with
  | nil => intro x; rfl
  | cons hop hops ih =>
    intro x
    simp only [List.foldl_cons,filterStep keep f absent neverReturn,ih]

/-- Exact whole-list guard commutation for a nonempty list of genuine
parts: replaying a filter on each selected original output agrees with
filtering the exact final original output. The empty-list case is deliberately
not claimed, since it would retain the untouched start. -/
theorem exact_OriginalPackedZeroFilterFold (xs : Entries) (s : Settings) (c ty : Nat)
    (hop : Nat) (tail : List Nat) (state : Option Nat) :
    (hop :: tail).foldl (fun x h => (packedCallback xs s c ty x h).filter retainsZero) state =
      ((hop :: tail).foldl (packedCallback xs s c ty) state).filter retainsZero := by
  have nonzero (a h b : Nat) (reject : retainsZero a = false)
      (actual : packedCallback xs s c ty (some a) h = some b) : retainsZero b = false := by
    have notZero : rawRank a ≠ 0 := by
      intro eq
      simp [retainsZero,eq] at reject
    have stay := exact_PackedCallbackNonzeroPersists xs s c ty a h b notZero actual
    cases outcome : retainsZero b with
    | false => rfl
    | true => exact False.elim (stay (by simpa only [retainsZero,beq_iff_eq] using outcome))
  simp only [List.foldl_cons]
  exact filterFold retainsZero (packedCallback xs s c ty)
    (packedAbsent xs s c ty) nonzero tail (packedCallback xs s c ty state hop)

#print axioms exact_PackedCallbackNonzeroPersists
#print axioms exact_OriginalPackedZeroFilterFold

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveFoldInvariantProof
