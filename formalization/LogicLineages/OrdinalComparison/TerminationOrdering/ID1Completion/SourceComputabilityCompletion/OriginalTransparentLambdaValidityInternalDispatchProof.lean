module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBranchSupportProof OriginalTransparentLambdaValidityInternalBranchValueProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open InternalBetaTotalityProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalControlGraphChoiceProof (excludedMiddle)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem underHyp {P : Formula alpha} (h : Nonempty (Derivation body Gamma P)) (q : Formula alpha) :
    Nonempty (Derivation body (q :: Gamma) P) :=
  weakenProof h (fun p hp => List.mem_cons_of_mem q hp)

theorem byCases (p psi : Formula alpha)
    (hy : Nonempty (Derivation body (p :: Gamma) psi))
    (hn : Nonempty (Derivation body (p.not :: Gamma) psi)) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

def dispatchFactors {alpha : Type} (old : Program 2) (out raw parameter : OTerm alpha)
    (lambdaFactors : Formula alpha) : Formula alpha :=
  (TagIs 2 raw ⊓ equal out (numeral 1)) ⊔
    ((TagIs 1 raw ⊓ lambdaFactors) ⊔
      ((TagIs 2 raw).not ⊓ ((TagIs 1 raw).not ⊓ graph2 old out raw parameter)))

theorem dispatchRecover (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (F : Formula alpha)
    (hL : Nonempty (Derivation body Gamma ((graph2 lambda out raw parameter).iff F)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter))) :
    Nonempty (Derivation body Gamma (dispatchFactors old out raw parameter F)) := by
  let T := TagIs 2 raw
  let L := TagIs 1 raw
  apply byCases T
  · have ht : Nonempty (Derivation body (T :: Gamma) T) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := andIntro ht (dispatchTwo old lambda out raw parameter ht (underHyp hg T))
    exact ⟨orLeft h⟩
  · have hn2 : Nonempty (Derivation body (T.not :: Gamma) T.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply byCases L
    · have ht : Nonempty (Derivation body (L :: T.not :: Gamma) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hl⟩ := dispatchOne old lambda out raw parameter ht (underHyp (underHyp hg T.not) L)
      obtain ⟨hL'⟩ := underHyp (underHyp hL T.not) L
      obtain ⟨ht⟩ := ht
      exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction ht
        (Derivation.implicationElimination (Derivation.conjunctionLeft hL') hl)))⟩
    · have hn1 : Nonempty (Derivation body (L.not :: T.not :: Gamma) L.not) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hn2' := underHyp hn2 L.not
      have ho := dispatchOpaque old lambda out raw parameter hn2' hn1 (underHyp (underHyp hg T.not) L.not)
      obtain ⟨h⟩ := andIntro hn2' (andIntro hn1 ho)
      exact ⟨orRight (orRight h)⟩

theorem dispatchValue (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (F : Formula alpha)
    (hL : Nonempty (Derivation body Gamma ((graph2 lambda out raw parameter).iff F)))
    (hf : Nonempty (Derivation body Gamma (dispatchFactors old out raw parameter F))) :
    Nonempty (Derivation body Gamma (graph2 (rootDispatch old lambda) out raw parameter)) := by
  let A := TagIs 2 raw ⊓ equal out (numeral 1)
  let B := TagIs 1 raw ⊓ F
  let C := (TagIs 2 raw).not ⊓ ((TagIs 1 raw).not ⊓ graph2 old out raw parameter)
  let G := graph2 (rootDispatch old lambda) out raw parameter
  have ha : Nonempty (Derivation body (A :: Gamma) G) := by
    have h : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact dispatchTwoValue old lambda out raw parameter (andLeft h) (andRight h)
  have hb : Nonempty (Derivation body (B :: Gamma) G) := by
    have h : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hL'⟩ := underHyp hL B
    obtain ⟨hF⟩ := andRight h
    exact dispatchOneValue old lambda out raw parameter (andLeft h)
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hL') hF⟩
  have hc : Nonempty (Derivation body (C :: Gamma) G) := by
    have h : Nonempty (Derivation body (C :: Gamma) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact dispatchOpaqueValue old lambda out raw parameter (andLeft h)
      (andLeft (andRight h)) (andRight (andRight h))
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  obtain ⟨hc⟩ := hc
  obtain ⟨hf⟩ := hf
  have hbc : Derivation body Gamma ((B ⊔ C).imp G) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction hb) _) (addHyp (Derivation.implicationIntroduction hc) _))
  exact ⟨disjunctionElimination hf (Derivation.implicationIntroduction ha) hbc⟩

theorem dispatchEquation (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (F : Formula alpha)
    (hL : Nonempty (Derivation body Gamma ((graph2 lambda out raw parameter).iff F))) :
    Nonempty (Derivation body Gamma
      ((graph2 (rootDispatch old lambda) out raw parameter).iff
        (dispatchFactors old out raw parameter F))) := by
  let A := graph2 (rootDispatch old lambda) out raw parameter
  let B := dispatchFactors old out raw parameter F
  obtain ⟨hf⟩ := dispatchRecover old lambda out raw parameter F (underHyp hL A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := dispatchValue old lambda out raw parameter F (underHyp hL B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDispatchProof
