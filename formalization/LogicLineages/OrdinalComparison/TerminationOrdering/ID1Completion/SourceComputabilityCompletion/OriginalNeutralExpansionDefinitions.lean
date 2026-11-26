module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansion
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalAccessibilityRules
open SourceComputabilityFormulaSupportProof (numeral allOne)

/-- Every successor in the ORIGINAL source relation is computable. The edge
retains its original existential certificate graph; no raw quotient relation,
selected list decoder or supplied proof oracle replaces that relation. -/
def computableSuccessors {alpha : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (object : OTerm alpha) : Formula alpha :=
  allOne
    ((edge src false context (object.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (computable comp tau (numeral context) (.var (.inr (0 : Fin 1)))))

/-- The immediate neutral-application consumer: original computable reducts
of the function and an original computable same-Gamma argument make every
original source-certificate successor of the accepted application computable.
The function itself is NOT assumed computable, and the final endpoint need
not be an application or have a non-lambda function reduct. -/
def applicationPremises {alpha : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (function argument out target witness : OTerm alpha) : Formula alpha :=
  typed comp (.arrow sigma tau) (numeral context) function ⊓
    (OriginalSourceNeutralApplication.nonLambdaObject function ⊓
      (computableSuccessors src comp context (.arrow sigma tau) function ⊓
        (guarded comp function argument ⊓
          (computable comp sigma (numeral context) argument ⊓
            (accepted comp sigma tau (numeral context) function argument out ⊓
              certificate src false context out target witness)))))

def ApplicationSuccessorComputability (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
    (function argument out target witness : OTerm alpha),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    ((applicationPremises src comp context sigma tau function argument out target witness).imp
      (computable comp tau (numeral context) target)))

/-- Genuine all-finite-type neutral expansion in the original combined-body
calculus. Only original typing, the non-lambda Object test, and original
computable source successors are assumed. No scalar/arrow computability of
the source, external accessibility, window-member premise or substituted
source relation is admitted. -/
def NeutralComputabilityExpansion (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (tau : Ty) (alpha : Type) (Gamma : List (Formula alpha)) (object : OTerm alpha),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    ((typed comp tau (numeral context) object ⊓
      (OriginalSourceNeutralApplication.nonLambdaObject object ⊓
        computableSuccessors src comp context tau object)).imp
      (computable comp tau (numeral context) object)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansion
