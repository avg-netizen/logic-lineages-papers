module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalBetaTotalityProof
open InternalAcceptanceConjunctionProof
open InternalQuotientComparisonProof (orLeft orRight)
open OriginalTransparentLambdaValidityInternal (BooleanOutput)
open OriginalTransparentLambdaValidityInternalBooleanProof (booleanEquation)
open OriginalTransparentLambdaValidityInternalBranchSupportProof (conjunctionReject)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem iffSelf (A : Formula alpha) : Nonempty (Derivation body Gamma (A.iff A)) :=
  ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

theorem iffReverse {A B : Formula alpha}
    (h : Nonempty (Derivation body Gamma (A.iff B))) :
    Nonempty (Derivation body Gamma (B.iff A)) :=
  andIntro (andRight h) (andLeft h)

theorem iffCompose {A B C : Formula alpha}
    (hab : Nonempty (Derivation body Gamma (A.iff B)))
    (hbc : Nonempty (Derivation body Gamma (B.iff C))) :
    Nonempty (Derivation body Gamma (A.iff C)) := by
  obtain ⟨hab⟩ := hab
  obtain ⟨hbc⟩ := hbc
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionLeft hbc) A)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hab) A)
        (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight hab) C)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hbc) C)
        (Derivation.hypothesis List.mem_cons_self))))⟩

theorem andIff {A B C D : Formula alpha}
    (hac : Nonempty (Derivation body Gamma (A.iff C)))
    (hbd : Nonempty (Derivation body Gamma (B.iff D))) :
    Nonempty (Derivation body Gamma ((A ⊓ B).iff (C ⊓ D))) := by
  obtain ⟨hac⟩ := hac
  obtain ⟨hbd⟩ := hbd
  have hleft : Derivation body (A ⊓ B :: Gamma) (A ⊓ B) := Derivation.hypothesis List.mem_cons_self
  have hright : Derivation body (C ⊓ D :: Gamma) (C ⊓ D) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hac) (A ⊓ B))
        (Derivation.conjunctionLeft hleft))
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hbd) (A ⊓ B))
        (Derivation.conjunctionRight hleft))))
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hac) (C ⊓ D))
        (Derivation.conjunctionLeft hright))
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hbd) (C ⊓ D))
        (Derivation.conjunctionRight hright))))⟩

theorem notIff {A B : Formula alpha}
    (hab : Nonempty (Derivation body Gamma (A.iff B))) :
    Nonempty (Derivation body Gamma (A.not.iff B.not)) := by
  obtain ⟨hab⟩ := hab
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination
          (addHyp (addHyp (Derivation.conjunctionRight hab) A.not) B)
          (Derivation.hypothesis List.mem_cons_self)))))
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination
          (addHyp (addHyp (Derivation.conjunctionLeft hab) B.not) A)
          (Derivation.hypothesis List.mem_cons_self)))))⟩

theorem orIff {A B C D : Formula alpha}
    (hac : Nonempty (Derivation body Gamma (A.iff C)))
    (hbd : Nonempty (Derivation body Gamma (B.iff D))) :
    Nonempty (Derivation body Gamma ((A ⊔ B).iff (C ⊔ D))) := by
  obtain ⟨hac⟩ := hac
  obtain ⟨hbd⟩ := hbd
  have forward : Derivation body Gamma ((A ⊔ B).imp (C ⊔ D)) := by
    apply Derivation.implicationIntroduction
    apply disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
    · exact Derivation.implicationIntroduction (orLeft (Derivation.implicationElimination
        (addHyp (addHyp (Derivation.conjunctionLeft hac) (A ⊔ B)) A)
        (Derivation.hypothesis List.mem_cons_self)))
    · exact Derivation.implicationIntroduction (orRight (Derivation.implicationElimination
        (addHyp (addHyp (Derivation.conjunctionLeft hbd) (A ⊔ B)) B)
        (Derivation.hypothesis List.mem_cons_self)))
  have backward : Derivation body Gamma ((C ⊔ D).imp (A ⊔ B)) := by
    apply Derivation.implicationIntroduction
    apply disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
    · exact Derivation.implicationIntroduction (orLeft (Derivation.implicationElimination
        (addHyp (addHyp (Derivation.conjunctionRight hac) (C ⊔ D)) C)
        (Derivation.hypothesis List.mem_cons_self)))
    · exact Derivation.implicationIntroduction (orRight (Derivation.implicationElimination
        (addHyp (addHyp (Derivation.conjunctionRight hbd) (C ⊔ D)) D)
        (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨Derivation.conjunctionIntroduction forward backward⟩

theorem booleanIff (out : OTerm alpha) {A B : Formula alpha}
    (hab : Nonempty (Derivation body Gamma (A.iff B))) :
    Nonempty (Derivation body Gamma ((BooleanOutput out A).iff (BooleanOutput out B))) :=
  orIff (andIff (iffSelf _) hab) (andIff (iffSelf _) (notIff hab))

/-- Full output of the original exact-one conjunction, with no Boolean
assumption about either callback. Non-one callbacks reject literally. -/
theorem conjunctionEquation {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (out : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((programGraph (InternalAcceptance.conjunction p q) out xs).iff
        (BooleanOutput out (programGraph p (numeral 1) xs ⊓
          programGraph q (numeral 1) xs)))) := by
  let F := programGraph p (numeral 1) xs ⊓ programGraph q (numeral 1) xs
  let A := programGraph (InternalAcceptance.conjunction p q) (numeral 1) xs
  obtain ⟨hy⟩ := conjunctionAccept (body := body) (Gamma := F :: Gamma) p q xs
    (andLeft (show Nonempty (Derivation body (F :: Gamma) F) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩))
    (andRight (show Nonempty (Derivation body (F :: Gamma) F) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have hna : Nonempty (Derivation body (F.not :: Gamma) A.not) := by
    obtain ⟨hf⟩ := conjunctionRecover (body := body) (Gamma := A :: F.not :: Gamma) p q xs
      (show Nonempty (Derivation body (A :: F.not :: Gamma) A) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
      (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) hf)⟩
  obtain ⟨hn⟩ := conjunctionReject p q xs hna
  exact booleanEquation (InternalAcceptance.conjunction p q) xs out F
    ⟨Derivation.implicationIntroduction hy⟩ ⟨Derivation.implicationIntroduction hn⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
