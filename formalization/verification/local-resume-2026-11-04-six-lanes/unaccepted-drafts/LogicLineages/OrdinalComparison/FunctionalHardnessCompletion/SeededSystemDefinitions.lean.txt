module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem
open OriginalDomain FunctionalDetector SourceCollisionCompletion

def Solves {n : Nat} (s : System n) (ρ : AdmissibleSubstitution (SignedPair.Context n)) : Prop :=
  ∀ d∈s,SignedPair.meaning (SeededCompiler.seededInputs ρ) (SeededCompiler.subtractSeed d)=0

/-- One actual source system: each original unknown is shared, and each
alignment pair is fresh. The seed is a literal closed source in each compiled
pair, not an extra free name or an assumed ordinal-valued primitive. -/
def compile {n : Nat} : System n → CompiledSystem n
  | [] => ⟨SignedPair.Context n,(fun {_} x => x),[]⟩
  | d::ds =>
      let tail := compile ds
      let p := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair
      let a := p.1.rename tail.original
      let b := p.2.rename tail.original
      ⟨.ground::.ground::tail.context,
       (fun {_} x => shiftTwo tail.context (tail.original x)),
       (left (alignedLeft a) (alignedRight b),right (alignedLeft a) (alignedRight b))::
         tail.detectors.map (fun p =>
           (p.1.rename (shiftTwo tail.context),p.2.rename (shiftTwo tail.context)))⟩

def strictPair {n : Nat} (s : System n) :=
  SourceAggregateCompletion.aggregate (compile s).detectors

def weakPair {n : Nat} (s : System n) :=
  (ParametricLiteralWeakWrapper.constantApply (strictPair s).2,
   ParametricLiteralWeakWrapper.identityApply (strictPair s).1)

def universalStrict {n : Nat} (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution (compile s).context,
    rawScalar (valuation ρ) (strictPair s).2<rawScalar (valuation ρ) (strictPair s).1

def universalWeak {n : Nat} (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution (compile s).context,
    rawScalar (valuation ρ) (weakPair s).1≤rawScalar (valuation ρ) (weakPair s).2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem
