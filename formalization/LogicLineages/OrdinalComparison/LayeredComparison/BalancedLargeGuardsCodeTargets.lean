module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Targets
open CommonHeadCompiler (encode)

/-- Exact default lookup, faithful fixed-head identity and actual ordinal
order, followed by literal equality with the accepted two key formulas.
This applies to ALL indices, including positions beyond the head list. -/
def ExactHeadsAndKeys : Prop :=
  rawNoteEncode (0 : NONote).1 = 0 ∧
  ∀ (heads : List NONote) (i j : Nat),
    headCode (encodeHeads heads) i = rawNoteEncode (heads.getD i 0).1 ∧
    (headCode (encodeHeads heads) i = headCode (encodeHeads heads) j ↔
      heads.getD i 0 = heads.getD j 0) ∧
    rawComparisonCode (headCode (encodeHeads heads) i) (headCode (encodeHeads heads) j) =
      orderingCode (ONote.cmp (heads.getD i 0).1 (heads.getD j 0).1) ∧
    (rawComparisonCode (headCode (encodeHeads heads) i) (headCode (encodeHeads heads) j) = 0 ↔
      (heads.getD i 0).1.repr < (heads.getD j 0).1.repr) ∧
    keyEqualCode (encodeHeads heads) i j =
      encode (BalancedLargeGuards.keyEqualFormula (fun k => heads.getD k 0) i j) ∧
    keyLessCode (encodeHeads heads) i j =
      encode (BalancedLargeGuards.keyLessFormula (fun k => heads.getD k 0) i j)

/-- Exact postfix lists, not merely equivalent truth values. The original
mask order, stable filtering, occurrence order, duplicates, negative guards
and explicit right-fold neutral elements are all retained. -/
def ExactFiniteGuardCode : Prop := ∀ heads : List NONote,
  (∀ (m i : Nat) (mask : List Bool),
    maskCode (encodeHeads heads) m i mask =
      encode (BalancedLargeGuards.maskGuard (fun k => heads.getD k 0) m i mask)) ∧
  (∀ (cs : List Int) (i : Nat) (desired : Int),
    blockCode (encodeHeads heads) cs i desired =
      encode (BalancedLargeGuards.blockFormula (fun k => heads.getD k 0) cs i desired)) ∧
  (∀ cs : List Int,
    canceledCode (encodeHeads heads) cs =
      encode (BalancedLargeGuards.canceledFormula (fun k => heads.getD k 0) cs)) ∧
  (∀ (cs : List Int) (i : Nat),
    maximalCode (encodeHeads heads) cs i =
      encode (BalancedLargeGuards.maximalFormula (fun k => heads.getD k 0) cs i))

/-- Generic large-branch code is EXACTLY the existing formula encoding, for
every supplied threshold, finite normal-head list and integer coefficient
list. No list-length, distinctness, sign or validity hypotheses are imposed.
The two final labels still denote the actual lower parts upon later source
instantiation; no new source payload adapter is part of this target. -/
def ExactLargeGuardCode : Prop :=
  (∀ (left right : Nat) (desired : Int),
    differenceSignCode left right desired =
      encode (BalancedLargeGuards.differenceSignFormula left right desired)) ∧
  (∀ (heads : List NONote) (cs : List Int) (desired : Int),
    signCode (encodeHeads heads) cs desired =
      encode (BalancedLargeGuards.signFormula (fun k => heads.getD k 0) cs desired)) ∧
  ∀ (L : Nat) (heads : List NONote) (cs : List Int) (desired : Int),
    largeCode L (encodeHeads heads) cs desired =
      encode (BalancedLargeGuards.largeFormula L (fun k => heads.getD k 0) cs desired)

/-- All ten new numeric transforms are uniformly primitive recursive on
arbitrary raw head lists, signed coefficient lists, masks and scalar inputs.
No normality, length agreement, valid source payload, ordinal evaluation or
precomputed head-comparison oracle is supplied as a premise. -/
def UniformPrimitiveRecursive : Prop :=
  Primrec₂ headCode ∧
  Primrec (fun p : List Nat × Nat × Nat => keyEqualCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × Nat × Nat => keyLessCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × Nat × Nat × List Bool => maskCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : List Nat × List Int × Nat × Int => blockCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec₂ canceledCode ∧
  Primrec (fun p : List Nat × List Int × Nat => maximalCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Int => differenceSignCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × List Int × Int => signCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Int × Int => largeCode p.1 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Targets
