module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.SixCoordinateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof (OTerm eqn)
open InternalTagArithmeticSupportProof (symm refl)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem coordinate_relation {A : Type} (R : A → A → Prop)
    (a b c d e f g h i j k l : A)
    (h0 : R a g) (h1 : R b h) (h2 : R c i) (h3 : R d j)
    (h4 : R e k) (h5 : R f l) :
    ∀ n : Fin 6, R (![a,b,c,d,e,f] n) (![g,h,i,j,k,l] n) := by
  intro n
  refine Fin.cases h0 (fun n => Fin.cases h1 (fun n => Fin.cases h2 (fun n =>
    Fin.cases h3 (fun n => Fin.cases h4 (fun n => Fin.cases h5 (fun n => Fin.elim0 n) n) n) n) n) n) n

theorem coordinates (extrasSide : Bool)
    (label f g recorded base dest extraTypes extras otherExtras : OTerm alpha)
    (hhead : Nonempty (Derivation body Delta (eqn f g)))
    (hsibling : Nonempty (Derivation body Delta (eqn (if extrasSide then base else extras) (if extrasSide then dest else otherExtras)))) :
    ∀ i : Fin 6, Nonempty (Derivation body Delta (eqn
      (![label,f,recorded,if extrasSide then base else dest,extraTypes,if extrasSide then otherExtras else extras] i)
      (![label,g,recorded,dest,extraTypes,otherExtras] i))) := by
  apply coordinate_relation (fun x y : OTerm alpha => Nonempty (Derivation body Delta (eqn x y)))
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
