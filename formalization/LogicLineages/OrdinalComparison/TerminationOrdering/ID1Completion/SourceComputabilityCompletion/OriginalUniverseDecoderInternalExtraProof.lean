module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalExtraProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderInternalBranchProof OriginalUniverseDecoderInternalBooleanProof
open OriginalUniverseDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The literal three constructor-sensitive alternatives of the frozen guard. -/
def extraCondition (M W : Program 2) (v d h c : OTerm alpha) : Formula alpha :=
  (equal v (numeral 1) ⊓ graph2 M (numeral 1) d c) ⊔
    ((equal v (numeral 4) ⊓ graph2 W (numeral 1) d c) ⊔
      ((equal v (numeral 5) ⊓ graph2 W (numeral 1) h c) ⊔
        ((equal v (numeral 1)).not ⊓
          ((equal v (numeral 4)).not ⊓ (equal v (numeral 5)).not))))

theorem extraForward (M W : Program 2) (r c v d h : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag v r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hh : Nonempty (Derivation body Delta (graph2 numberedHead h r c)))
    (ho : Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (extraCondition M W v d h c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  let q5 := ifSame tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
  let q4 := ifSame tag (constant 2 4) (oneIf (windowAt W domain)) q5
  apply formulaCases (equal v (numeral 1)) _
  · have he : Nonempty (Derivation body (equal v (numeral 1) :: Delta) (equal v (numeral 1))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg := sameYesElim tag (constant 2 1) (oneIf (memberAt M domain)) (q4)
      (numeral 1) v (numeral 1) xs (withHyp hv _) (constantValue 1 xs) he (withHyp ho _)
    have ht := binaryRecover M domain context (numeral 1) d c xs
      (andLeft (filterForward (memberAt M domain) (constant 2 1) xs hg)) (withHyp hd _) (projectionValue 1 xs)
    obtain ⟨hc⟩ := andIntro he ht
    exact ⟨orLeft hc⟩
  · have hn0 : Nonempty (Derivation body ((equal v (numeral 1)).not :: Delta) (equal v (numeral 1)).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hnext0 := sameNoElim tag (constant 2 1) (oneIf (memberAt M domain)) (q4)
      (numeral 1) v (numeral 1) xs (withHyp hv _) (constantValue 1 xs) hn0 (withHyp ho _)
    apply formulaCases (equal v (numeral 4)) _
    · have he : Nonempty (Derivation body (equal v (numeral 4) :: (equal v (numeral 1)).not :: Delta) (equal v (numeral 4))) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hg := sameYesElim tag (constant 2 4) (oneIf (windowAt W domain)) (q5)
        (numeral 1) v (numeral 4) xs (withHyp (withHyp hv _) _) (constantValue 4 xs) he (withHyp hnext0 _)
      have ht := binaryRecover W domain context (numeral 1) d c xs
        (andLeft (filterForward (windowAt W domain) (constant 2 1) xs hg)) (withHyp (withHyp hd _) _) (projectionValue 1 xs)
      obtain ⟨hc⟩ := andIntro he ht
      exact ⟨orRight (orLeft hc)⟩
    · have hn1 : Nonempty (Derivation body ((equal v (numeral 4)).not :: (equal v (numeral 1)).not :: Delta) (equal v (numeral 4)).not) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hnext1 := sameNoElim tag (constant 2 4) (oneIf (windowAt W domain)) (q5)
        (numeral 1) v (numeral 4) xs (withHyp (withHyp hv _) _) (constantValue 4 xs) hn1 (withHyp hnext0 _)
      apply formulaCases (equal v (numeral 5)) _
      · have he : Nonempty (Derivation body (equal v (numeral 5) :: (equal v (numeral 4)).not :: (equal v (numeral 1)).not :: Delta) (equal v (numeral 5))) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        have hg := sameYesElim tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
          (numeral 1) v (numeral 5) xs (withHyp (withHyp (withHyp hv _) _) _) (constantValue 5 xs) he (withHyp hnext1 _)
        have ht := binaryRecover W numberedHead context (numeral 1) h c xs
          (andLeft (filterForward (windowAt W numberedHead) (constant 2 1) xs hg)) (withHyp (withHyp (withHyp hh _) _) _) (projectionValue 1 xs)
        obtain ⟨hc⟩ := andIntro he ht
        exact ⟨orRight (orRight (orLeft hc))⟩
      · have hn2 : Nonempty (Derivation body ((equal v (numeral 5)).not :: (equal v (numeral 4)).not :: (equal v (numeral 1)).not :: Delta) (equal v (numeral 5)).not) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        have hnext2 := sameNoElim tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
          (numeral 1) v (numeral 5) xs (withHyp (withHyp (withHyp hv _) _) _) (constantValue 5 xs) hn2 (withHyp hnext1 _)
        obtain ⟨hc⟩ := andIntro (withHyp (withHyp hn0 _) _) (andIntro (withHyp hn1 _) hn2)
        exact ⟨orRight (orRight (orRight hc))⟩

theorem extraBackward (M W : Program 2) (r c v d h : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag v r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hh : Nonempty (Derivation body Delta (graph2 numberedHead h r c)))
    (ho : Nonempty (Derivation body Delta (extraCondition M W v d h c))) :
    Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  let q5 := ifSame tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)
  let q4 := ifSame tag (constant 2 4) (oneIf (windowAt W domain)) q5
  let A := equal v (numeral 1) ⊓ graph2 M (numeral 1) d c
  let B := equal v (numeral 4) ⊓ graph2 W (numeral 1) d c
  let C := equal v (numeral 5) ⊓ graph2 W (numeral 1) h c
  let D := (equal v (numeral 1)).not ⊓ ((equal v (numeral 4)).not ⊓ (equal v (numeral 5)).not)
  apply orCases ho
  · have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply sameYesIntro tag (constant 2 1) (oneIf (memberAt M domain)) q4 (numeral 1) v (numeral 1) xs
      (withHyp hv _) (constantValue 1 xs) (andLeft ha)
    exact filterBackward (memberAt M domain) (constant 2 1) xs
      (binaryValue M domain context (numeral 1) d c xs (andRight ha) (withHyp hd _) (projectionValue 1 xs))
      (constantValue 1 xs)
  · have hrest : Nonempty (Derivation body ((B ⊔ (C ⊔ D)) :: Delta) (B ⊔ (C ⊔ D))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases hrest
    · have hb : Nonempty (Derivation body (B :: (B ⊔ (C ⊔ D)) :: Delta) B) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameNoIntro tag (constant 2 1) (oneIf (memberAt M domain)) q4 (numeral 1) v (numeral 1) xs
        (withHyp (withHyp hv _) _) (constantValue 1 xs) (excludeNumeral v 4 1 (by decide) (andLeft hb))
      apply sameYesIntro tag (constant 2 4) (oneIf (windowAt W domain)) q5 (numeral 1) v (numeral 4) xs
        (withHyp (withHyp hv _) _) (constantValue 4 xs) (andLeft hb)
      exact filterBackward (windowAt W domain) (constant 2 1) xs
        (binaryValue W domain context (numeral 1) d c xs (andRight hb)
          (withHyp (withHyp hd _) _) (projectionValue 1 xs)) (constantValue 1 xs)
    · have hlast : Nonempty (Derivation body ((C ⊔ D) :: (B ⊔ (C ⊔ D)) :: Delta) (C ⊔ D)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases hlast
      · have hc : Nonempty (Derivation body (C :: (C ⊔ D) :: (B ⊔ (C ⊔ D)) :: Delta) C) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply sameNoIntro tag (constant 2 1) (oneIf (memberAt M domain)) q4 (numeral 1) v (numeral 1) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 1 xs) (excludeNumeral v 5 1 (by decide) (andLeft hc))
        apply sameNoIntro tag (constant 2 4) (oneIf (windowAt W domain)) q5 (numeral 1) v (numeral 4) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 4 xs) (excludeNumeral v 5 4 (by decide) (andLeft hc))
        apply sameYesIntro tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1) (numeral 1) v (numeral 5) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 5 xs) (andLeft hc)
        exact filterBackward (windowAt W numberedHead) (constant 2 1) xs
          (binaryValue W numberedHead context (numeral 1) h c xs (andRight hc)
            (withHyp (withHyp (withHyp hh _) _) _) (projectionValue 1 xs)) (constantValue 1 xs)
      · have hd' : Nonempty (Derivation body (D :: (C ⊔ D) :: (B ⊔ (C ⊔ D)) :: Delta) D) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply sameNoIntro tag (constant 2 1) (oneIf (memberAt M domain)) q4 (numeral 1) v (numeral 1) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 1 xs) (andLeft hd')
        apply sameNoIntro tag (constant 2 4) (oneIf (windowAt W domain)) q5 (numeral 1) v (numeral 4) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 4 xs) (andLeft (andRight hd'))
        exact sameNoIntro tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1) (numeral 1) v (numeral 5) xs
          (withHyp (withHyp (withHyp hv _) _) _) (constantValue 5 xs) (andRight (andRight hd')) (constantValue 1 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalExtraProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalExtraProof
