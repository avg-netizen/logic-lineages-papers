module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixesTargets
import LogicLineages.PermittedControl.ActualRawCanonicalZeroReplayPrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesPrimitiveProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodePrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualRawCanonicalZeroReplay (AnswerCode SequenceCode stepCode stepPrimitive)
open ActualRawCanonicalAnswerTapes (candidateTapesPrimitive)
open ActualCanonicalOperandGroupingCode (groupRawPrimitive)

theorem availablePrimitive : Primrec available :=
  candidateTapesPrimitive.comp (groupRawPrimitive.comp Primrec.snd)

private def stepInputs (p : Candidate × AnswerCode) : RawSyntax × AnswerCode := (p.1.2,p.2)

private theorem stepInputsPrimitive : Primrec stepInputs :=
  (Primrec.snd.comp Primrec.fst).pair Primrec.snd

private def childResult (p : (Candidate × AnswerCode) × RawSyntax) : Candidate :=
  (p.1.1.1 ++ [p.1.2],p.2)

private theorem childResultPrimitive : Primrec childResult := by
  let P := (Candidate × AnswerCode) × RawSyntax
  have tapes : Primrec (fun p : P => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have answer : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have out : Primrec (Prod.snd : P → RawSyntax) := Primrec.snd
  exact (Primrec.list_concat.comp tapes answer).pair out

private theorem extendLiteral (p : Candidate × AnswerCode) :
    (stepCode (stepInputs p)).map (fun st => childResult (p,st)) = extendCandidate p := rfl

theorem extendPrimitive : Primrec extendCandidate :=
  (Primrec.option_map (stepPrimitive.comp stepInputsPrimitive) childResultPrimitive.to₂).of_eq extendLiteral

theorem childrenPrimitive : Primrec children := by
  have ready : Primrec (fun p : Candidate => available p.2) := availablePrimitive.comp Primrec.snd
  exact Primrec.listFilterMap ready extendPrimitive.to₂

theorem nextLevelPrimitive : Primrec nextLevel :=
  Primrec.list_flatMap Primrec.id (childrenPrimitive.comp Primrec.snd).to₂

private def initial (st : RawSyntax) : List Candidate := [([],st)]

private theorem initialPrimitive : Primrec initial :=
  Primrec.list_cons.comp ((Primrec.const ([] : SequenceCode)).pair Primrec.id) (Primrec.const [])

private theorem iterateLiteral (p : RawSyntax × Nat) :
    p.2.rec (initial p.1) (fun _ acc => nextLevel acc) = level p.1 p.2 := by
  rcases p with ⟨start,n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextLevel (n.rec (initial start) (fun _ acc => nextLevel acc)) =
      nextLevel (level start n)
    rw [ih]

private theorem iteratePrimitive :
    Primrec (fun p : RawSyntax × Nat => level p.1 p.2) := by
  let A := RawSyntax × Nat
  let R := A × (Nat × List Candidate)
  have fuel : Primrec (Prod.snd : A → Nat) := Primrec.snd
  have init : Primrec (fun p : A => initial p.1) := initialPrimitive.comp Primrec.fst
  have acc : Primrec (fun p : R => p.2.2) := Primrec.snd.comp Primrec.snd
  have advance : Primrec (fun p : R => nextLevel p.2.2) := nextLevelPrimitive.comp acc
  exact (Primrec.nat_rec' fuel init advance.to₂).of_eq iterateLiteral

theorem levelPrimitive : Primrec₂ level := iteratePrimitive.to₂

private theorem prefixesUncurried :
    Primrec (fun p : Nat × RawSyntax => prefixes p.1 p.2) := by
  let A := Nat × RawSyntax
  have indices : Primrec (fun p : A => List.range (p.1+1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have select : Primrec₂ (fun (p : A) k => level p.2 k) :=
    levelPrimitive.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  exact Primrec.list_flatMap indices select

theorem prefixesPrimitive : Primrec₂ prefixes := prefixesUncurried.to₂

theorem exactRawZeroPrefixEffectivity : ExactRawZeroPrefixEffectivity :=
  ⟨availablePrimitive,nextLevelPrimitive,levelPrimitive,prefixesPrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes
