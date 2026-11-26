module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduction (a b c d e f r56 r456 r3456 r23456 r123456 k h t base ts extra p56 p456 p3456 p23456 p123456 : OTerm alpha)
    (hg56 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r56 e f)))
    (hp56 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p56 ts extra)))
    (hg456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r456 d r56)))
    (hp456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p456 base p56)))
    (hg3456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r3456 c r456)))
    (hp3456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3456 t p456)))
    (hg23456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r23456 b r3456)))
    (hp23456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p23456 h p3456)))
    (hg123456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r123456 a r23456)))
    (hp123456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p123456 k p23456)))
    (hma : Nonempty (Derivation body Delta (graph2 contains (numeral 1) a k)))
    (hmb : Nonempty (Derivation body Delta (graph2 contains (numeral 1) b h)))
    (hmc : Nonempty (Derivation body Delta (graph2 contains (numeral 1) c t)))
    (hmd : Nonempty (Derivation body Delta (graph2 contains (numeral 1) d base)))
    (hme : Nonempty (Derivation body Delta (graph2 contains (numeral 1) e ts)))
    (hmf : Nonempty (Derivation body Delta (graph2 contains (numeral 1) f extra)))
    : Nonempty (Derivation body Delta (graph2 contains (numeral 1) r123456 p123456)) := by
  have hm56 := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce e f r56 p56 ts extra hg56 (andIntro hme hmf) hp56
  have hm456 := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce d r56 r456 p456 base p56 hg456 (andIntro hmd hm56) hp456
  have hm3456 := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce c r456 r3456 p3456 t p456 hg3456 (andIntro hmc hm456) hp3456
  have hm23456 := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce b r3456 r23456 p23456 h p3456 hg23456 (andIntro hmb hm3456) hp23456
  have hm123456 := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce a r23456 r123456 p123456 k p23456 hg123456 (andIntro hma hm23456) hp123456
  exact hm123456

theorem elimination (a b c d e f r56 r456 r3456 r23456 r123456 k h t base ts extra p56 p456 p3456 p23456 p123456 : OTerm alpha)
    (hg56 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r56 e f)))
    (hp56 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p56 ts extra)))
    (hg456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r456 d r56)))
    (hp456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p456 base p56)))
    (hg3456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r3456 c r456)))
    (hp3456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3456 t p456)))
    (hg23456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r23456 b r3456)))
    (hp23456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p23456 h p3456)))
    (hg123456 : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross r123456 a r23456)))
    (hp123456 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p123456 k p23456)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) r123456 p123456))) :
    Nonempty (Derivation body Delta
      (graph2 contains (numeral 1) a k ⊓ graph2 contains (numeral 1) b h ⊓
       graph2 contains (numeral 1) c t ⊓ graph2 contains (numeral 1) d base ⊓
       graph2 contains (numeral 1) e ts ⊓ graph2 contains (numeral 1) f extra)) := by
  have h123456 := NumericDependencyCross.CrossProof.projection a r23456 r123456 p123456 k p23456 hg123456 hm hp123456
  have h23456 := NumericDependencyCross.CrossProof.projection b r3456 r23456 p23456 h p3456 hg23456 (andRight h123456) hp23456
  have h3456 := NumericDependencyCross.CrossProof.projection c r456 r3456 p3456 t p456 hg3456 (andRight h23456) hp3456
  have h456 := NumericDependencyCross.CrossProof.projection d r56 r456 p456 base p56 hg456 (andRight h3456) hp456
  have h56 := NumericDependencyCross.CrossProof.projection e f r56 p56 ts extra hg56 (andRight h456) hp56
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andLeft h123456) (andLeft h23456)) (andLeft h3456)) (andLeft h456)) (andLeft h56)) (andRight h56)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductsProof
