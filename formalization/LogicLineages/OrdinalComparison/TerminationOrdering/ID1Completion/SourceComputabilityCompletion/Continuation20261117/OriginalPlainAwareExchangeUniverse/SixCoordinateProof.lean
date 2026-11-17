module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.SixCoordinateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem coordinates (extrasSide : Bool)
    (label f g recorded base dest extraTypes extras otherExtras : OTerm alpha)
    (hhead : Nonempty (Derivation body Delta (eqn f g)))
    (hsibling : Nonempty (Derivation body Delta (eqn (if extrasSide then base else extras) (if extrasSide then dest else otherExtras)))) :
    ∀ i : Fin 6, Nonempty (Derivation body Delta (eqn
      (![label,f,recorded,if extrasSide then base else dest,extraTypes,if extrasSide then otherExtras else extras] i)
      (![label,g,recorded,dest,extraTypes,otherExtras] i))) := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i =>
    Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i) i) i) i
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.SixCoordinateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.SixCoordinateProof
