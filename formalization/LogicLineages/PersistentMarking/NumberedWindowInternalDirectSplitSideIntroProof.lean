module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledCertificateIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawBoundaryIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetIntroProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSplitSideIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectCoreTargets (Cut)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalDirectBoundaryGuardsTargets (BoundaryReports)
open NumberedWindowInternalConsUnionReportBuildProof (Report unionReportOfGraphs)
open NumberedWindowInternalDirectRawBoundaryIntroProof (exact_OriginalRawBoundaryFromReports)
open NumberedWindowInternalDirectRawTargetIntroProof (exact_OriginalRawTargetFromReports)
open NumberedWindowInternalDirectInstalledCertificateIntroProof (exact_LiteralInstalledOddCertificateIntro)

/-- Actual reports needed of one changed component, with source, target,
kept, removed and inserted raw fields and fixed physical parse outputs.
No alternative obstruction or retained-only step is allowed. -/
structure OriginalChangedSide (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} (Γ : List (Formula α))
    (s t kept removed inserted ds dt dk dd projected sourceJoin targetJoin dh dTail : OTerm α) : Prop where
  boundary : BoundaryReports (sourceBody (literalData i r) c) Γ s t removed ds dt dd dh dTail i
  keptParse : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc dk) ![kept]
  rowTargets : Report (B := sourceBody (literalData i r) c) (Γ := Γ) insertedTargets (suc projected) ![inserted]
  sourceAppend : Report (B := sourceBody (literalData i r) c) (Γ := Γ) append sourceJoin ![dk,dd]
  targetAppend : Report (B := sourceBody (literalData i r) c) (Γ := Γ) append targetJoin ![dk,projected]
  sourceCount : Report (B := sourceBody (literalData i r) c) (Γ := Γ) permutation (suc z) ![ds,sourceJoin]
  targetCount : Report (B := sourceBody (literalData i r) c) (Γ := Γ) permutation (suc z) ![dt,targetJoin]
  rowScan : Report (B := sourceBody (literalData i r) c) (Γ := Γ) (scan r) (suc z) ![inserted,removed]

/-- Construct the genuine literal checker tag-5 certificate for a changed
component once its real partition, insertion and typing side reports
are supplied. This pays certificate reconstruction, not the arithmetic
that supplies these reports from one original whole-list certificate. -/
theorem exact_LiteralChangedSideCertificate (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)}
    (s t kept removed inserted ds dt dk dd projected sourceJoin targetJoin dh dTail : OTerm α)
    (p : OriginalChangedSide i r c Γ s t kept removed inserted ds dt dk dd projected sourceJoin targetJoin dh dTail) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ
      (certificate (literalData i r) true c s t (tripleTerm 5 kept removed inserted))) := by
  let B := sourceBody (literalData i r) c
  have bd := exact_OriginalRawBoundaryFromReports i s t removed ds dt dd dh dTail p.boundary
  have so := unionReportOfGraphs permutation kept removed s dk dd ds sourceJoin
    ⟨p.boundary.parsed.source,p.keptParse,p.boundary.parsed.removed⟩ p.sourceAppend p.sourceCount
  have ta := exact_OriginalRawTargetFromReports permutation t kept inserted dt dk projected targetJoin
    p.boundary.parsed.kept p.keptParse p.rowTargets p.targetAppend p.targetCount
  have cutoff : Cut i r permutation B Γ s t kept removed inserted := ⟨bd,so,ta,p.rowScan⟩
  exact exact_LiteralInstalledOddCertificateIntro i r c s t kept removed inserted cutoff

#print axioms exact_LiteralChangedSideCertificate
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSplitSideIntroProof
