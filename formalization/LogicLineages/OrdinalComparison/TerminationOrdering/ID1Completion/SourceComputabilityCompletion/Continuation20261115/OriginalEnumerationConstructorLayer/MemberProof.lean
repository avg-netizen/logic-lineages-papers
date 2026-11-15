module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.FrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.MemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open FrameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem merge {p q r : Formula alpha}
    (hp : Nonempty (Derivation body Delta (p.imp r)))
    (hq : Nonempty (Derivation body Delta (q.imp r))) :
    Nonempty (Derivation body Delta ((p ⊔ q).imp r)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationIntroduction (InternalBetaTotalityProof.disjunctionElimination
    (Derivation.hypothesis List.mem_cons_self)
    (InternalBetaTotalityProof.addHyp hp _) (InternalBetaTotalityProof.addHyp hq _))⟩

theorem inject0 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 0) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orLeft h⟩

theorem inject1 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 1) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orLeft h)⟩

theorem inject2 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 2) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orLeft h))⟩

theorem inject3 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 3) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orRight (orLeft h)))⟩

theorem inject4 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 4) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orRight (orRight (orLeft h))))⟩

theorem inject5 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 5) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orRight (orRight (orRight (orLeft h)))))⟩

theorem inject6 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 6) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orRight (orRight (orRight (orRight (orLeft h))))))⟩

theorem inject7 (ys : Fin 14 → OTerm alpha) (code : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 7) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  obtain ⟨h⟩ := hm
  exact ⟨orRight (orRight (orRight (orRight (orRight (orRight (orRight (h)))))))⟩

theorem forward1 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 8) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 0) code
  let R := graph2 contains (numeral 1) (ys 1) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 0) (ys 1) (ys 8) code
    (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) hm
  obtain ⟨hl⟩ := inject0 ys code (Delta := L :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject1 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward2 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 9) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 8) code
  let R := graph2 contains (numeral 1) (ys 2) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 8) (ys 2) (ys 9) code
    (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) hm
  obtain ⟨hl⟩ := forward1 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject2 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward3 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 10) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 9) code
  let R := graph2 contains (numeral 1) (ys 3) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 9) (ys 3) (ys 10) code
    (andRight (andLeft (andLeft (andLeft (andLeft hf))))) hm
  obtain ⟨hl⟩ := forward2 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject3 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward4 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 11) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 10) code
  let R := graph2 contains (numeral 1) (ys 4) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 10) (ys 4) (ys 11) code
    (andRight (andLeft (andLeft (andLeft hf)))) hm
  obtain ⟨hl⟩ := forward3 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject4 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward5 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 12) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 11) code
  let R := graph2 contains (numeral 1) (ys 5) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 11) (ys 5) (ys 12) code
    (andRight (andLeft (andLeft hf))) hm
  obtain ⟨hl⟩ := forward4 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject5 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward6 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 13) code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 12) code
  let R := graph2 contains (numeral 1) (ys 6) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 12) (ys 6) (ys 13) code
    (andRight (andLeft hf)) hm
  obtain ⟨hl⟩ := forward5 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject6 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem forward7 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.branchMember (part ys) code)) := by
  let L := graph2 contains (numeral 1) (ys 13) code
  let R := graph2 contains (numeral 1) (ys 7) code
  obtain ⟨hs⟩ := PrimaryExpansionSoundness.AppendProof.appendPreservation (ys 13) (ys 7) out code
    (andRight hf) hm
  obtain ⟨hl⟩ := forward6 ys out code (withHyp hf L) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := inject7 ys code (Delta := R :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hs
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem backward0 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 0) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h1 := PrimaryExpansion.PreservationProof.appendPreservation (ys 0) (ys 1) (ys 8) code (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) hm
  have h2 := PrimaryExpansion.PreservationProof.appendPreservation (ys 8) (ys 2) (ys 9) code (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) h1
  have h3 := PrimaryExpansion.PreservationProof.appendPreservation (ys 9) (ys 3) (ys 10) code (andRight (andLeft (andLeft (andLeft (andLeft hf))))) h2
  have h4 := PrimaryExpansion.PreservationProof.appendPreservation (ys 10) (ys 4) (ys 11) code (andRight (andLeft (andLeft (andLeft hf)))) h3
  have h5 := PrimaryExpansion.PreservationProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) h4
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward1 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 1) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h1 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 0) (ys 1) (ys 8) code (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) hm
  have h2 := PrimaryExpansion.PreservationProof.appendPreservation (ys 8) (ys 2) (ys 9) code (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) h1
  have h3 := PrimaryExpansion.PreservationProof.appendPreservation (ys 9) (ys 3) (ys 10) code (andRight (andLeft (andLeft (andLeft (andLeft hf))))) h2
  have h4 := PrimaryExpansion.PreservationProof.appendPreservation (ys 10) (ys 4) (ys 11) code (andRight (andLeft (andLeft (andLeft hf)))) h3
  have h5 := PrimaryExpansion.PreservationProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) h4
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward2 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 2) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h2 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 8) (ys 2) (ys 9) code (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) hm
  have h3 := PrimaryExpansion.PreservationProof.appendPreservation (ys 9) (ys 3) (ys 10) code (andRight (andLeft (andLeft (andLeft (andLeft hf))))) h2
  have h4 := PrimaryExpansion.PreservationProof.appendPreservation (ys 10) (ys 4) (ys 11) code (andRight (andLeft (andLeft (andLeft hf)))) h3
  have h5 := PrimaryExpansion.PreservationProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) h4
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward3 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 3) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h3 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 9) (ys 3) (ys 10) code (andRight (andLeft (andLeft (andLeft (andLeft hf))))) hm
  have h4 := PrimaryExpansion.PreservationProof.appendPreservation (ys 10) (ys 4) (ys 11) code (andRight (andLeft (andLeft (andLeft hf)))) h3
  have h5 := PrimaryExpansion.PreservationProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) h4
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward4 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 4) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h4 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 10) (ys 4) (ys 11) code (andRight (andLeft (andLeft (andLeft hf)))) hm
  have h5 := PrimaryExpansion.PreservationProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) h4
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward5 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h5 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 11) (ys 5) (ys 12) code (andRight (andLeft (andLeft hf))) hm
  have h6 := PrimaryExpansion.PreservationProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) h5
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward6 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 6) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h6 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 12) (ys 6) (ys 13) code (andRight (andLeft hf)) hm
  have h7 := PrimaryExpansion.PreservationProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) h6
  exact h7

theorem backward7 (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (ys 7) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h7 := PrimaryEdgeInclusion.AppendRightProof.appendPreservation (ys 13) (ys 7) out code (andRight hf) hm
  exact h7

theorem backward (ys : Fin 14 → OTerm alpha) (out code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (facts ys out)))
    (hm : Nonempty (Derivation body Delta (Targets.branchMember (part ys) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  let M0 := graph2 contains (numeral 1) (ys 0) code
  obtain ⟨b0⟩ := backward0 ys out code (withHyp hf M0) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h0 : Nonempty (Derivation body Delta (M0.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b0⟩
  let M1 := graph2 contains (numeral 1) (ys 1) code
  obtain ⟨b1⟩ := backward1 ys out code (withHyp hf M1) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 : Nonempty (Derivation body Delta (M1.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b1⟩
  let M2 := graph2 contains (numeral 1) (ys 2) code
  obtain ⟨b2⟩ := backward2 ys out code (withHyp hf M2) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h2 : Nonempty (Derivation body Delta (M2.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b2⟩
  let M3 := graph2 contains (numeral 1) (ys 3) code
  obtain ⟨b3⟩ := backward3 ys out code (withHyp hf M3) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h3 : Nonempty (Derivation body Delta (M3.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b3⟩
  let M4 := graph2 contains (numeral 1) (ys 4) code
  obtain ⟨b4⟩ := backward4 ys out code (withHyp hf M4) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h4 : Nonempty (Derivation body Delta (M4.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b4⟩
  let M5 := graph2 contains (numeral 1) (ys 5) code
  obtain ⟨b5⟩ := backward5 ys out code (withHyp hf M5) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h5 : Nonempty (Derivation body Delta (M5.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b5⟩
  let M6 := graph2 contains (numeral 1) (ys 6) code
  obtain ⟨b6⟩ := backward6 ys out code (withHyp hf M6) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h6 : Nonempty (Derivation body Delta (M6.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b6⟩
  let M7 := graph2 contains (numeral 1) (ys 7) code
  obtain ⟨b7⟩ := backward7 ys out code (withHyp hf M7) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h7 : Nonempty (Derivation body Delta (M7.imp (graph2 contains (numeral 1) out code))) :=
    ⟨Derivation.implicationIntroduction b7⟩
  obtain ⟨h⟩ := (merge h0 (merge h1 (merge h2 (merge h3 (merge h4 (merge h5 (merge h6 h7)))))))
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.MemberProof
