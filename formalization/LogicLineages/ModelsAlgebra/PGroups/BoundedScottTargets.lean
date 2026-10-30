module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableTargets
public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Countability pays existence of the actual finite/aleph0 invariant table. -/
def groupCountableUlmTableExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ),
    ∃ entries : Fin N → Option ℕ, ∀ j : Fin N,
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) =
        (match entries j with | none => Cardinal.aleph0 | some m => (m : Cardinal))

/-- General Pi3 upper bound, relative to actual countable additive groups.
This does not assert the source's sharp lower/upper case classification. -/
def groupBoundedPiThreeScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) →
      ∃ entries : Fin N → Option ℕ,
        Complexity .pi (3 : Ordinal.{0}) (boundedUlmTable p N entries) ∧
        GroupScottSentence G (boundedUlmTable p N entries)

end LogicLineages.ModelsAlgebra.PGroups.Targets
