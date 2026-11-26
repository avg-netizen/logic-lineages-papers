module
public import LogicLineages.PermittedControl.FixedEntryProgramDefinitions
public import LogicLineages.PermittedControl.InverseTableDefinitions
public import LogicLineages.PermittedControl.OutputOffsetDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

abbrev IntervalPairCodes := (Nat×Nat)×(Nat×Nat)
abbrev SignedShiftCodes := (Nat×Nat)×(Nat×Nat)

def intervalPairCodes (lp mp lq mq : NONote) : IntervalPairCodes :=
  ((rawNoteEncode lp.1,rawNoteEncode mp.1),(rawNoteEncode lq.1,rawNoteEncode mq.1))

/-- Real raw implementation of the complete semantic inverse-table tail. -/
def inverseTableTailCode (lambda mu nu delta B : Nat) : Nat :=
  let kappa := ordinalAddCode mu delta
  let lambdaQ := ordinalAddCode nu delta
  1+max (max 2 (max (rawNormCode lambda) (max (rawNormCode kappa) (rawNormCode mu))))
    (max (encodedGapInputTail (kappa,mu,lambdaQ,nu,0))
      (max (encodedGapInputTail (lambdaQ,nu,kappa,mu,0))
        (equalGapCertificateTailCode mu nu delta B)))

def thresholdTailCode (p : IntervalPairCodes) (B : Nat) : Nat :=
  max (inverseTableTailCode p.1.1 p.1.2 p.2.2 (ordinalSubCode p.2.1 p.2.2) B)
    (inverseTableTailCode p.2.1 p.2.2 p.1.2 (ordinalSubCode p.1.1 p.1.2) B)

def reverseComparisonCode (c : Nat) : Nat := if c=0 then 2 else if c=2 then 0 else 1

/-- Returns P-versus-Q order; the source printed rows are Q-versus-P. -/
def inverseTableDecisionCode (sign y h : Nat) : Nat :=
  if sign=1 then numericalComparison h y else
  if sign=2 then (if y≤h then 2 else 0) else (if y<h then 2 else 0)

/-- Finite source decision: only H entry maps are evaluated in unequal-gap
branches. P and Q output values are not secretly computed by this program. -/
def thresholdProgram (f : Nat → Nat) (z : IntervalPairCodes×(Nat×Nat)) : Part Nat :=
  let p := z.1
  let x := z.2.1
  let y := z.2.2
  let dp := ordinalSubCode p.1.1 p.1.2
  let dq := ordinalSubCode p.2.1 p.2.2
  let gapOrder := rawComparisonCode dq dp
  if gapOrder=1 then Part.some
    (if x<y then 0 else if y<x then 2 else equalGapCertificateCode p.1.2 p.2.2 dp)
  else if gapOrder=0 then
    (fixedEntryProgram f (p.1.1,ordinalAddCode p.1.2 dq,x)).map
      (fun r => inverseTableDecisionCode (equalGapCertificateCode p.1.2 p.2.2 dq) y r.1)
  else
    (fixedEntryProgram f (p.2.1,ordinalAddCode p.2.2 dp,y)).map
      (fun r => reverseComparisonCode
        (inverseTableDecisionCode (equalGapCertificateCode p.2.2 p.1.2 dp) x r.1))

def signedOffsetMagnitudeCode (c : Nat) : Nat := c/2+c%2

def signedTranslateCode (c x : Nat) : Nat :=
  if c%2=0 then x+c/2 else x-(c/2+1)

def signedComparisonCode (a b : Nat) : Nat :=
  if a%2=0 then
    if b%2=0 then numericalComparison (a/2) (b/2) else 2
  else if b%2=0 then 0 else numericalComparison (b/2) (a/2)

def integerComparison (a b : Int) : Nat := if a<b then 0 else if a=b then 1 else 2

/-- Input translations stay literal, with a computable margin for every
input domain and the signed output collision bound. -/
def translatedThresholdTailCode (p : IntervalPairCodes) (s : SignedShiftCodes) (B : Nat) : Nat :=
  thresholdTailCode p B + signedOffsetMagnitudeCode s.1.1 + signedOffsetMagnitudeCode s.1.2 +
    signedOffsetMagnitudeCode s.2.1 + signedOffsetMagnitudeCode s.2.2 + 2

def translatedThresholdProgram (f : Nat → Nat)
    (z : (IntervalPairCodes×SignedShiftCodes)×(Nat×Nat)) : Part Nat :=
  (thresholdProgram f (z.1.1,(signedTranslateCode z.1.2.1.1 z.2.1,
    signedTranslateCode z.1.2.1.2 z.2.2))).map
      (fun c => if c=1 then signedComparisonCode z.1.2.2.1 z.1.2.2.2 else c)

end LogicLineages.PermittedControl
