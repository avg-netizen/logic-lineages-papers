module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalChoicesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalChoicesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def termBranchSpec (H : Program 1) (out g t p suffix : OTerm alpha) : Fin 8 → Formula alpha :=
  ![StepVariable out g t p suffix,StepLambda out g t p suffix,StepApplication out g t p suffix,
    StepBottom out t p suffix,StepOrdinary H out g t p suffix,StepNumbered H out g t p suffix,
    equal out (numeral 0),equal out (numeral 0)]

def argumentsBranchSpec (out g t p suffix : OTerm alpha) : Fin 8 → Formula alpha :=
  ![equal out (numeral 0),equal out (numeral 0),equal out (numeral 0),equal out (numeral 0),
    equal out (numeral 0),equal out (numeral 0),StepArgumentsNil out t p suffix,
    StepArgumentsCons out g t p suffix]

/-- All eight constructor tags and their simultaneous exclusion are split
inside the proof calculus. This is not a native natural-number case split. -/
theorem tagCover (value : OTerm alpha) :
    Nonempty (Derivation body Delta
      (alternatives 8 (fun i => equal value (numeral i.val)) (StepUnknownTag value))) := by
  apply formulaCases (equal value (numeral 0)) _
  · exact alternativesIntro 8 _ _ (0 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
  ·
    apply formulaCases (equal value (numeral 1)) _
    · exact alternativesIntro 8 _ _ (1 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
    ·
      apply formulaCases (equal value (numeral 2)) _
      · exact alternativesIntro 8 _ _ (2 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
      ·
        apply formulaCases (equal value (numeral 3)) _
        · exact alternativesIntro 8 _ _ (3 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
        ·
          apply formulaCases (equal value (numeral 4)) _
          · exact alternativesIntro 8 _ _ (4 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
          ·
            apply formulaCases (equal value (numeral 5)) _
            · exact alternativesIntro 8 _ _ (5 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
            ·
              apply formulaCases (equal value (numeral 6)) _
              · exact alternativesIntro 8 _ _ (6 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
              ·
                apply formulaCases (equal value (numeral 7)) _
                · exact alternativesIntro 8 _ _ (7 : Fin 8) ⟨Derivation.hypothesis List.mem_cons_self⟩
                ·
                  apply alternativesFallback 8
                  apply Nonempty.intro
                  exact Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (Derivation.conjunctionIntroduction (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_self))) (Derivation.hypothesis (List.mem_cons_self))))))))

theorem tagCases (value : OTerm alpha) (psi : Formula alpha)
    (known : ∀ (i : Fin 8) (Theta : List (Formula alpha)),
      (∀ p ∈ Delta, p ∈ Theta) → Nonempty (Derivation body Theta (equal value (numeral i.val))) →
      Nonempty (Derivation body Theta psi))
    (other : ∀ Theta : List (Formula alpha),
      (∀ p ∈ Delta, p ∈ Theta) → Nonempty (Derivation body Theta (StepUnknownTag value)) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) :=
  alternativesCases (fun i : Fin 8 => equal value (numeral i.val)) (StepUnknownTag value) psi
    (tagCover value) known other

theorem termSpecIntro (H : Program 1) (out g t value p suffix : OTerm alpha) (i : Fin 8)
    (h : Nonempty (Derivation body Delta
      (equal value (numeral i.val) ⊓ termBranchSpec H out g t p suffix i))) :
    Nonempty (Derivation body Delta (StepTermDispatch H out g t value p suffix)) :=
  alternativesIntro 8 (fun i => equal value (numeral i.val) ⊓ termBranchSpec H out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) i h

theorem termSpecFallback (H : Program 1) (out g t value p suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepUnknownTag value ⊓ equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (StepTermDispatch H out g t value p suffix)) :=
  alternativesFallback 8 (fun i => equal value (numeral i.val) ⊓ termBranchSpec H out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) h

theorem termSpecCases (H : Program 1) (out g t value p suffix : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepTermDispatch H out g t value p suffix)))
    (known : ∀ (i : Fin 8) (Theta : List (Formula alpha)),
      (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (equal value (numeral i.val) ⊓ termBranchSpec H out g t p suffix i)) →
      Nonempty (Derivation body Theta psi))
    (other : ∀ Theta : List (Formula alpha),
      (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (StepUnknownTag value ⊓ equal out (numeral 0))) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) :=
  alternativesCases (fun i : Fin 8 => equal value (numeral i.val) ⊓ termBranchSpec H out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) psi h known other

theorem argumentsSpecIntro (out g t value p suffix : OTerm alpha) (i : Fin 8)
    (h : Nonempty (Derivation body Delta
      (equal value (numeral i.val) ⊓ argumentsBranchSpec out g t p suffix i))) :
    Nonempty (Derivation body Delta (StepArgumentsDispatch out g t value p suffix)) :=
  alternativesIntro 8 (fun i => equal value (numeral i.val) ⊓ argumentsBranchSpec out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) i h

theorem argumentsSpecFallback (out g t value p suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepUnknownTag value ⊓ equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (StepArgumentsDispatch out g t value p suffix)) :=
  alternativesFallback 8 (fun i => equal value (numeral i.val) ⊓ argumentsBranchSpec out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) h

theorem argumentsSpecCases (out g t value p suffix : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepArgumentsDispatch out g t value p suffix)))
    (known : ∀ (i : Fin 8) (Theta : List (Formula alpha)),
      (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (equal value (numeral i.val) ⊓ argumentsBranchSpec out g t p suffix i)) →
      Nonempty (Derivation body Theta psi))
    (other : ∀ Theta : List (Formula alpha),
      (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (StepUnknownTag value ⊓ equal out (numeral 0))) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) :=
  alternativesCases (fun i : Fin 8 => equal value (numeral i.val) ⊓ argumentsBranchSpec out g t p suffix i)
    (StepUnknownTag value ⊓ equal out (numeral 0)) psi h known other

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
