module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem normalize (extrasSide : Bool)
    (right label f g recorded base dest extraTypes extras otherExtras : OTerm alpha)
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hhead : Nonempty (Derivation body Delta (eqn f g)))
    (hsibling : Nonempty (Derivation body Delta (eqn (if extrasSide then base else extras) (if extrasSide then dest else otherExtras)))) :
    Nonempty (Derivation body Delta (programGraph numberedConstructor right
      ![label,f,recorded,if extrasSide then base else dest,extraTypes,if extrasSide then otherExtras else extras])) := by
  apply NumberedInputProof.inputs right ![label,g,recorded,dest,extraTypes,otherExtras] _ hrc
  intro i
  fin_cases i
  · exact ⟨refl _⟩
  · exact hhead
  · exact ⟨refl _⟩
  · cases extrasSide
    · exact ⟨refl _⟩
    · exact hsibling
  · exact ⟨refl _⟩
  · cases extrasSide
    · exact hsibling
    · exact ⟨refl _⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralConstructorProof
