module
public import LogicLineages.CartierObserverCurrent.ProfileDescentTargets
public import LogicLineages.CartierObserverCurrent.RationalCoverageProof
public import LogicLineages.CartierObserverCurrent.F2DescentProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileDescent
open SplittingRoots

private noncomputable instance rootFintype (d : Nat) : Fintype (Root d) := by
  classical
  unfold Root
  infer_instance

private theorem square_value (d : Nat) (z : Root d) :
    (rootSquare d z).val = z.val ^ 2 := Classical.choose_spec (frobeniusRootPermutation d) z

private theorem map_constant (d : Nat) (x : FieldAt d) :
    Naturality.rationalMap (frobenius (FieldAt d) 2)
      (algebraMap (FieldAt d) (RatFunc (FieldAt d)) x) =
      algebraMap (FieldAt d) (RatFunc (FieldAt d)) (x ^ 2) := by
  rw [IsScalarTower.algebraMap_apply (FieldAt d) (Polynomial (FieldAt d)) (RatFunc (FieldAt d))]
  rw [Naturality.extensionPolynomial]
  change algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d))
    ((Polynomial.C x).map (frobenius (FieldAt d) 2)) = _
  rw [Polynomial.map_C]
  exact (IsScalarTower.algebraMap_apply (FieldAt d) (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) _).symm

theorem frobeniusTransport : Targets.FrobeniusTransport := by
  intro d b
  classical
  have hX : Naturality.rationalMap (frobenius (FieldAt d) 2)
      (Basic.rationalX : RatFunc (FieldAt d)) = Basic.rationalX := by
    simpa only [Basic.rationalX, Polynomial.map_X] using
      Naturality.extensionPolynomial (FieldAt d) (FieldAt d) (frobenius (FieldAt d) 2) Polynomial.X
  unfold RationalCoverage.reconstruct
  rw [map_sum]
  apply Fintype.sum_equiv (rootSquare d)
  intro z
  rw [map_div₀, map_sub, hX, map_constant, map_constant]
  simp only [transport, Equiv.symm_apply_apply, square_value]

private theorem transport_fixed (d : Nat) (b : Root d → FieldAt d) :
    transport d b = b ↔ compatible d b := by
  constructor
  · intro h z
    have hz := congrFun h (rootSquare d z)
    simpa only [transport, Equiv.symm_apply_apply] using hz.symm
  · intro h
    funext z
    have hz := h ((rootSquare d).symm z)
    simpa only [Equiv.apply_symm_apply] using hz.symm

theorem compatibilityFixed : Targets.CompatibilityFixed := by
  intro d b
  rw [frobeniusTransport, (RationalCoverage.reconstructionInjective d).eq_iff]
  exact (transport_fixed d b).symm

private theorem reconstructed_state (d : Nat) (b : Root d → FieldAt d) :
    RationalCoverage.state d (RationalCoverage.reconstruct d b) := by
  apply (RationalCoverage.statePresentation d _).mpr
  exact ⟨RationalCoverage.tupleNumerator d b, RationalCoverage.numeratorDegree d b,
    RationalCoverage.actualPartialFraction d b⟩

private theorem extended_fixed (d : Nat) (g : RatFunc (ZMod 2)) :
    Naturality.rationalMap (frobenius (FieldAt d) 2) (extend d g) = extend d g := by
  apply (F2Descent.rationalDescent d _).mpr
  exact ⟨g, rfl, fun h hh => (extend d).injective hh⟩

theorem profileToBase : Targets.ProfileToBase := by
  intro d b
  constructor
  · intro hb
    obtain ⟨g, hg, _⟩ := (F2Descent.rationalDescent d _).mp ((compatibilityFixed d b).mp hb)
    have hs := reconstructed_state d b
    have hbase : baseState d g := by
      constructor
      · apply (CanonicalExtension.properMap (ZMod 2) (FieldAt d) (algebraMap (ZMod 2) (FieldAt d)) g).mp
        rw [hg]
        exact hs.1
      · change (Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) g).denom ∣ _
        rw [hg]
        exact hs.2
    refine ⟨g, ⟨hbase, hg⟩, ?_⟩
    intro h hh
    exact (extend d).injective (hh.2.trans hg.symm)
  · rintro ⟨g, ⟨_, hg⟩, _⟩
    apply (compatibilityFixed d b).mpr
    rw [← hg]
    exact extended_fixed d g

theorem baseToProfile : Targets.BaseToProfile := by
  intro d g hg
  have hs : RationalCoverage.state d (extend d g) := by
    constructor
    · exact (CanonicalExtension.properMap (ZMod 2) (FieldAt d)
        (algebraMap (ZMod 2) (FieldAt d)) g).mpr hg.1
    · exact hg.2
  obtain ⟨b, hb, _⟩ := (RationalCoverage.reconstructionCoverage d _).mp hs
  have hc : compatible d b := by
    apply (compatibilityFixed d b).mpr
    rw [hb]
    exact extended_fixed d g
  refine ⟨b, ⟨hc, hb⟩, ?_⟩
  intro c hc
  exact RationalCoverage.reconstructionInjective d (hc.2.trans hb.symm)

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileDescent
end LogicLineages.CartierObserverCurrent.ProfileDescent
