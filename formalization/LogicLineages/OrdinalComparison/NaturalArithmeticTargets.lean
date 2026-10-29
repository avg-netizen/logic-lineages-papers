module
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions

@[expose] public section

/-! Independent actual-denotation and product-norm obligations for the source
natural arithmetic. No notation algorithm or correctness theorem is imported.
-/

namespace LogicLineages.OrdinalComparison.Targets

def NaturalSumDenotation (add : NONote → NONote → NONote) : Prop :=
  ∀ a b : NONote, (add a b).1.repr = ordinalNaturalSum a.1.repr b.1.repr

def NaturalProductDenotation (mul : NONote → NONote → NONote) : Prop :=
  ∀ a b : NONote, (mul a b).1.repr = ordinalNaturalProduct a.1.repr b.1.repr

def NaturalProductNormBound (mul : NONote → NONote → NONote) : Prop :=
  ∀ a b : NONote, Vendor.R1.treeWeight (mul a b).1 ≤
    Vendor.R1.treeWeight a.1 * Vendor.R1.treeWeight b.1

end LogicLineages.OrdinalComparison.Targets
