module
public import LogicLineages.PermittedControl.ActualEffectiveGlobalTailTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodePrimitiveProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.ThresholdNumericProgramsProof
import LogicLineages.OrdinalComparison.RawNormCode
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveGlobalTail
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassCommonTail ActualZeroEdgeAlphabetCode ActualNodeTailSupply
open ActualSyntaxChargeBudget ConcreteCountPairReplacement
open SelectedCountOnlyClass (omegaSquareNote)

private theorem normPrimitive : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

private theorem finiteMaxPrimitive {α β : Type} [Primcodable α] [Primcodable β]
    {items : α → List β} {cost : α → β → Nat}
    (sequence : Primrec items) (one : Primrec₂ cost) :
    Primrec (fun a => finiteMax (cost a) (items a)) := by
  let A := α × (β × Nat)
  have context : Primrec (fun p : A => p.1) := Primrec.fst
  have item : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have last : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr sequence (Primrec.const 0)
    (Primrec.nat_max.comp (one.comp context item) last).to₂

private theorem prefixChoicesPrimitive : Primrec prefixChoicesCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have rank : Primrec (fun op : LowerOperandCode => op.2.1) := Primrec.fst.comp Primrec.snd
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have lam := Primrec.fst.comp endpoints
  have mu := Primrec.snd.comp endpoints
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  have choice : Primrec prefixChoiceCode :=
    Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
      (Primrec.option_some.comp (rank.pair (lam.pair eta))) (Primrec.const none)
  exact Primrec.listFilterMap Primrec.id (choice.comp Primrec.snd).to₂

private theorem annotationPrimitive : Primrec annotationBoundCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have lam := normPrimitive.comp (Primrec.fst.comp endpoints)
  have mu := normPrimitive.comp (Primrec.snd.comp endpoints)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (Primrec.nat_max.comp lam (Primrec.nat_add.comp mu (Primrec.const 3))) (Primrec.const 0)

private theorem prefixAffordabilityPrimitive : Primrec₂ prefixAffordabilityCode := by
  let A := Nat × PrefixCode
  have B : Primrec (fun p : A => p.1) := Primrec.fst
  have ends : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have lam := normPrimitive.comp (Primrec.fst.comp ends)
  have eta := normPrimitive.comp (Primrec.snd.comp ends)
  exact (Primrec.nat_max.comp lam (Primrec.nat_max.comp
    (Primrec.nat_add.comp eta (Primrec.const 3))
    (Primrec.nat_max.comp (Primrec.const 1) B))).to₂

private theorem safeTailPrimitive : Primrec₂ safeTailCode := by
  let A := IntervalPairCodes × Nat
  have hp : Primrec (fun z : A => z.1.1) := Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun z : A => z.1.2) := Primrec.snd.comp Primrec.fst
  have hlp := Primrec.fst.comp hp
  have hmp := Primrec.snd.comp hp
  have hlq := Primrec.fst.comp hq
  have hmq := Primrec.snd.comp hq
  have inverse := inverseTableTailCode_primrec hlq hmq hmp
    (ordinalSubCodeEffective.comp hlp hmp) Primrec.snd
  have gap : Primrec (fun z : A =>
      encodedGapInputTail (z.1.1.1,z.1.1.2,z.1.2.1,z.1.2.2,0)) := by
    simpa only [encodedGapInputTail,Nat.mul_zero,Nat.add_zero] using
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.const 2) (normPrimitive.comp hlp))
          (normPrimitive.comp hlq))
        (Primrec.nat_max.comp (Primrec.const 1)
          (Primrec.nat_max.comp (normPrimitive.comp hmp) (normPrimitive.comp hmq))))
  exact Primrec.nat_max.comp inverse gap

private theorem labelsTailPrimitive : Primrec₂ labelsTailCode := by
  let A := Nat × List PrefixCode
  let P := A × PrefixCode
  let Q := P × PrefixCode
  have labels : Primrec (fun p : A => p.2) := Primrec.snd
  have bp : Primrec (fun q : Q => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have lo : Primrec (fun q : Q => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp Primrec.snd
  have pairCost : Primrec₂ (fun (p : P) (higher : PrefixCode) => pairTailCode p.1.1 p.2 higher) :=
    (safeTailPrimitive.comp (hi.pair lo) bp).to₂
  have inner : Primrec (fun p : P => finiteMax (pairTailCode p.1.1 p.2) p.1.2) :=
    finiteMaxPrimitive (labels.comp Primrec.fst) pairCost
  have outer : Primrec (fun p : A =>
      finiteMax (fun lower => finiteMax (pairTailCode p.1 lower) p.2) p.2) :=
    finiteMaxPrimitive labels inner.to₂
  have one : Primrec₂ (fun (p : A) l => prefixAffordabilityCode p.1 l) :=
    (prefixAffordabilityPrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.nat_max.comp (finiteMaxPrimitive labels one) outer).to₂

private theorem alphabetTailPrimitive : Primrec₂ alphabetTailCode := by
  let A := Nat × AlphabetCode
  have data : Primrec (fun p : A => p.2) := Primrec.snd
  have annotation : Primrec (fun p : A => finiteMax annotationBoundCode p.2) :=
    finiteMaxPrimitive data (annotationPrimitive.comp Primrec.snd).to₂
  have remaining := labelsTailPrimitive.comp (Primrec.fst : Primrec (Prod.fst : A → Nat))
    (prefixChoicesPrimitive.comp data)
  exact (Primrec.nat_max.comp annotation remaining).to₂

private theorem suppliedTailPrimitive :
    Primrec (fun p : Nat × Nat × AlphabetCode => suppliedTailCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × AlphabetCode
  have budget : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have alphabet : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact alphabetTailPrimitive.comp Primrec.fst
    (ActualZeroEdgeAlphabetCode.codeEffectivity.2.2.comp budget alphabet)

private theorem inputTailPrimitive :
    Primrec (fun p : Nat × Nat × List WeightedCode => inputTailCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List WeightedCode
  have ranks : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have keys : Primrec (fun p : A => p.2.2.map Prod.snd) :=
    Primrec.list_map terms (Primrec.snd.comp Primrec.snd).to₂
  exact suppliedTailPrimitive.comp
    (Primrec.fst.pair (((budgetCodeExact.1).comp ranks terms).pair keys))

theorem codeEffectivity : CodeEffectivity :=
  ⟨alphabetTailPrimitive,suppliedTailPrimitive,inputTailPrimitive⟩

end LogicLineages.PermittedControl.ActualEffectiveGlobalTail
