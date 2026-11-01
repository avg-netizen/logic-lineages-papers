module
public import LogicLineages.OrdinalComparison.ComparisonSignatureDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Genuine finite rank computation on the ACTUAL source order, with no
sorting or ordinal-comparison oracle. Every actual norm-bounded index lies
inside the finite carrier, and actual ordinal order strictly raises rank. -/
def ComparisonSignatureRankProgram : Prop :=
  Primrec₂ encodedComparisonSignatureRank ∧
  (∀ (budget : Nat) (eta : NONote), Vendor.R1.treeWeight eta.1≤budget →
    encodedComparisonSignatureRank budget (rawNoteEncode eta.1)<(encodedNormalNormBall budget).length) ∧
  ∀ (budget : Nat) (eta zeta : NONote),
    Vendor.R1.treeWeight eta.1≤budget → Vendor.R1.treeWeight zeta.1≤budget → eta.1.repr<zeta.1.repr →
    encodedComparisonSignatureRank budget (rawNoteEncode eta.1)<
      encodedComparisonSignatureRank budget (rawNoteEncode zeta.1)

/-- Entire initial-head principal expansion stays inside the actual finite
carrier; zero/successor raw heads are covered as syntax, not silently assumed
limit. Actual source valid limit heads supply positive exponents separately. -/
def ComparisonSignaturePrincipalCoverage : Prop :=
  ∀ (budget : Nat) (rho : NONote), Vendor.R1.treeWeight rho.1≤budget →
    ∀ eta∈principalExponentBlocks rho.1, rawNoteEncode eta∈encodedNormalNormBall budget

/-- Source successor normalization stays inside the SAME fixed carrier.
The exact unit drop in the additive source norm is derived, not an assumed
ordinal-order monotonicity property. -/
def ComparisonSignatureSuccessorClosure : Prop :=
  (∀ eta pred : NONote, eta.1.repr=pred.1.repr+1 →
    Vendor.R1.treeWeight eta.1=Vendor.R1.treeWeight pred.1+1) ∧
  ∀ (budget : Nat) (eta pred : NONote), Vendor.R1.treeWeight eta.1≤budget →
    eta.1.repr=pred.1.repr+1 → rawNoteEncode pred.1∈encodedNormalNormBall budget

end LogicLineages.OrdinalComparison.Targets
