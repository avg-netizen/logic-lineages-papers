module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedFiniteUniverse NumberedHeadCodecPrimrec NumberedHeadCodecPrimrecSupportProof
open NumberedHeadSignaturePrimrecProof

/-- Membership is uniform in the element and the actual list, including duplicates. -/
theorem memberPrimitive (A : Type) [Primcodable A] :
    PrimrecRel (fun (a : A) (xs : List A) => a ∈ xs) := by
  have h : PrimrecRel (fun (xs : List A) (a : A) => ∃ b ∈ xs, b = a) :=
    PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel (@Eq A))
  exact h.swap.of_eq (by intro a xs; simp)

/-- Every actual list entry must belong to the second list. -/
theorem membersPrimitive (A : Type) [Primcodable A] :
    PrimrecRel (fun (xs ys : List A) => ∀ a ∈ xs, a ∈ ys) :=
  (memberPrimitive A).forall_mem_list

def rankedSymbol (n : Nat) : HeadCode (Fin n) → Option (Fin n)
  | .ranked s => some s
  | _ => none

theorem rankedSymbolPrimitive (n : Nat) : Primrec (rankedSymbol n) := by
  have h : Primrec (fun data : HeadData n => data.elim
      (fun _ => (none : Option (Fin n)))
      (Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
        (Sum.elim (fun _ => none) some)))) :=
    sumElim (Primrec.const none) (sumElim (Primrec.const none)
      (sumElim (Primrec.const none) (sumElim (Primrec.const none) Primrec.option_some)))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

def rankedCoveredTest (n : Nat) (p : List (Fin n) × HeadCode (Fin n)) : Bool :=
  match rankedSymbol n p.2 with
  | none => true
  | some s => decide (s ∈ p.1)

theorem rankedCoveredTestPrimitive (n : Nat) : Primrec (rankedCoveredTest n) := by
  have h : Primrec (fun p : List (Fin n) × HeadCode (Fin n) =>
      (Option.casesOn (rankedSymbol n p.2) true
        (fun s => decide (s ∈ p.1)) : Bool)) :=
    Primrec.option_casesOn ((rankedSymbolPrimitive n).comp Primrec.snd)
      (Primrec.const true)
      (((memberPrimitive (Fin n)).decide).comp Primrec.snd
        (Primrec.fst.comp Primrec.fst)).to₂
  exact h.of_eq (by
    intro p
    unfold rankedCoveredTest
    cases rankedSymbol n p.2 <;> rfl)

theorem rankedCoveredCalibration (n : Nat) (symbols : List (Fin n))
    (head : HeadCode (Fin n)) :
    rankedCoveredTest n (symbols, head) = true ↔ RankedCovered symbols (decodeHead head) := by
  cases head <;> simp [rankedCoveredTest, rankedSymbol, RankedCovered, decodeHead]

theorem rankedCoveredPrimitive (n : Nat) :
    PrimrecPred (fun p : List (Fin n) × HeadCode (Fin n) =>
      RankedCovered p.1 (decodeHead p.2)) :=
  (Primrec.eq.comp (rankedCoveredTestPrimitive n) (Primrec.const true)).of_eq
    (fun p => rankedCoveredCalibration n p.1 p.2)

theorem headWindowPrimitive : NumberedHeadWindowPrimrecTargets.ActualHeadWindowPrimitive := by
  intro n arity
  have hcovered : PrimrecPred (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
      RankedCovered p.1 (decodeHead p.2.2)) :=
    (rankedCoveredPrimitive n).comp
      (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have hresult : PrimrecPred (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
      headResult (decodeHead p.2.2) ∈ p.2.1) :=
    (memberPrimitive Ty).comp
      ((headResultPrimitive n).comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  have harguments : PrimrecPred (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
      ∀ tau ∈ headArguments arity (decodeHead p.2.2), tau ∈ p.2.1) :=
    (membersPrimitive Ty).comp
      ((headArgumentsPrimitive n arity).comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  have h : PrimrecPred (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
      HeadInWindow arity p.1 p.2.1 (decodeHead p.2.2)) :=
    hcovered.and (hresult.and harguments)
  exact h.decide

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
