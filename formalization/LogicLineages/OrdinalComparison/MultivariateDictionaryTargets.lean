module
public import LogicLineages.OrdinalComparison.MultivariateDictionaryDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateDictionaryCanonicalInsertion : Prop :=
  (∀ (rho : NONote) (A : MultivariateCollectedNF) (a : Nat) (tags : MultivariateCollectedTags),
    MultivariateDictionaryOrdered tags →
      MultivariateDictionaryOrdered (multivariateCollectedTagInsert rho A a tags)) ∧
  (∀ left right : MultivariateCollectedTags, MultivariateDictionaryOrdered right →
    MultivariateDictionaryOrdered (multivariateCollectedTagsMerge left right))

def MultivariateDictionaryCoefficients : Prop :=
  (∀ (k : Nat) (rho : NONote) (A : MultivariateCollectedNF) (a : Nat) (tags : MultivariateCollectedTags),
    multivariateDictionaryCoefficient k (multivariateCollectedTagInsert rho A a tags)=
      (if k=multivariateCollectedTagKey rho A then a else 0)+multivariateDictionaryCoefficient k tags) ∧
  (∀ (k : Nat) (left right : MultivariateCollectedTags),
    multivariateDictionaryCoefficient k (multivariateCollectedTagsMerge left right)=
      multivariateDictionaryCoefficient k left+multivariateDictionaryCoefficient k right)

def MultivariateDictionaryCanonicalExtensionality : Prop :=
  ∀ A B : MultivariateCollectedTags, MultivariateDictionaryOrdered A → MultivariateDictionaryOrdered B →
    (∀ k : Nat, multivariateDictionaryCoefficient k A=multivariateDictionaryCoefficient k B) → A=B

/-- Actual structural algebra of canonical coefficient-vector/dictionary
storage. No semantic equality solver is substituted for structural equality. -/
def MultivariateCollectedStructuralAlgebra : Prop :=
  (∀ A B : MultivariateCollectedNF, MultivariateCollectedRootOrdered B →
    MultivariateCollectedRootOrdered (multivariateCollectedAdd A B)) ∧
  (∀ A B : MultivariateCollectedNF, MultivariateCollectedRootOrdered A →
    MultivariateCollectedRootOrdered B → multivariateCollectedAdd A B=multivariateCollectedAdd B A) ∧
  (∀ A B C : MultivariateCollectedNF, MultivariateCollectedRootOrdered C →
    multivariateCollectedAdd (multivariateCollectedAdd A B) C=
      multivariateCollectedAdd A (multivariateCollectedAdd B C)) ∧
  (∀ A : MultivariateCollectedNF,
    multivariateCollectedAdd (.mk 0 [] .nil) A=A) ∧
  (∀ A : MultivariateCollectedNF, MultivariateCollectedRootOrdered A →
    multivariateCollectedAdd A (.mk 0 [] .nil)=A)

end LogicLineages.OrdinalComparison.Targets
