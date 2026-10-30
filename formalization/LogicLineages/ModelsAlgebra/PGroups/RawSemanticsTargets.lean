module
public import LogicLineages.ModelsAlgebra.PGroups.RawSemanticsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth
universe u

def groupRawTermAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (t : GroupTerm n),
    rawTermEval (RawGroupStructure.ofGroup G) a t = t.eval a

def groupRawQFAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (q : QF n),
    q.RawRealize (RawGroupStructure.ofGroup G) a ↔ q.Realize a

def groupRawFormulaAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (φ : Formula n),
    φ.RawRealize (RawGroupStructure.ofGroup G) a ↔ φ.Realize a

end LogicLineages.ModelsAlgebra.PGroups.Targets
