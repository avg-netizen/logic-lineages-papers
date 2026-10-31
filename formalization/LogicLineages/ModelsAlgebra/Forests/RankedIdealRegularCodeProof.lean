module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosureStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProductStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStateStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.Proof
open RankedParse RankedGraphImage RankedIdealComponents

theorem atomExact : Targets.AtomExact := by
  intro t
  cases t <;> simp [language, atom, atomMachine, RankedIdealRegular.language,
    ProfileAutomatonEncoding.machineRun]

theorem atomIdeal : Targets.AtomIdeal := by
  constructor
  · exact ⟨.atom, (atomExact .atom).mpr rfl⟩
  · intro s t hst ht
    have he := (atomExact t).mp ht
    subst t
    cases hst
    exact (atomExact .atom).mpr rfl
  · intro s t hs ht
    have hes := (atomExact s).mp hs
    have het := (atomExact t).mp ht
    subst s
    subst t
    exact ⟨.atom, (atomExact .atom).mpr rfl, .atom, .atom⟩

theorem componentExact : Targets.ComponentExact := by
  intro C q t
  exact RankedIdealRegularState.StatementChecks.stateLanguageExact C.machine q t

theorem productExact : Targets.ProductExact := by
  intro o A B t
  exact RankedIdealRegularProduct.StatementChecks.downwardProductExact o A.machine B.machine t

theorem linearExact : Targets.LinearExact := by
  intro seed n rules t
  letI : ∀ i, DecidableEq (viewRule (rules i)).side.State := fun i => (rules i).side.stateDecidableEq
  exact RankedIdealRegularClosure.StatementChecks.downwardStarExact seed.machine n
    (fun i => viewRule (rules i)) t

theorem productIdeal : Targets.ProductIdeal := by
  intro o A B hA hB
  have he : language (product o A B) = RankedIdealConstructors.product o (language A) (language B) :=
    funext (fun t => propext (productExact o A B t))
  rw [he]
  exact RankedIdealConstructors.StatementChecks.productIdeal o (language A) (language B) hA hB

theorem linearIdeal : Targets.LinearIdeal := by
  intro seed n rules hs
  have he : language (linear seed rules) =
      RankedIdealConstructors.linearPiece (RankedIdealRegular.allowed (fun i => viewRule (rules i)))
        (language seed) := funext (fun t => propext (linearExact seed n rules t))
  rw [he]
  exact RankedIdealConstructors.StatementChecks.linearPieceIdeal _ _ hs

theorem componentIdeal : Targets.ComponentIdeal := by
  intro C q hq
  exact RankedIdealRegularState.StatementChecks.compiledNonlinearIdeal C.machine q hq
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.Proof
