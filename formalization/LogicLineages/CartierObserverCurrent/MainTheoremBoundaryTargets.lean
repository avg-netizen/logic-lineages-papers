module
public import LogicLineages.CartierObserverCurrent.FullThetaEntryTargets
public import LogicLineages.CartierObserverCurrent.FullOmegaBlockTargets

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Targets
open LogicLineages.OrdinalComparison

/-- Current20 thm:main, fourth item, first sentence: the first omega^omega
block of the ACTUAL descent from omega^(omega+1)+(v-4), for every v>=4.
After the entry step of lem:entry the state is the retained prefix p of
norm e=u-4 followed by the head block of total norm u; the next H actual
steps under the unchanged control Phi are the literal copy deletion counted
by H=H_e(u) of prop:omega-block, which ends at p plus a finite ordinal and
stays at or above p+omega before that; and the parity of H is the printed
equation (delta) with B=Phi u, C=Phi(u+1), d=B-u+3. Nothing is asserted
about the later copies of the same theta segment. -/
def LinkedFirstBlock : Prop :=
  ∀ v : Nat, 4 ≤ v →
    let Θ : Ordinal.{0} := Ordinal.omega0 ^ (Ordinal.omega0 + 1)
    let a : Ordinal.{0} := Θ + ((v - 4 : Nat) : Ordinal)
    let u := Phi v
    let q := (u - 1) / 3
    let p : Ordinal.{0} := Ordinal.omega0 ^ Ordinal.omega0 * ((q - 1 : Nat) : Ordinal)
    let e := u - 4
    let d := Phi u - u + 3
    let H := actualOmegaCopyCount e u
    actualOrdinalNorm a = v ∧ actualOrdinalNorm p = e ∧
    actualDescentStep a =
      p + actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - e) ∧
    (∀ i : Nat, i ≤ H →
      actualControlledStateAfter Phi (actualDescentStep a) i = p + actualOmegaCopyState e u i) ∧
    (∃ n : Nat, actualControlledStateAfter Phi (actualDescentStep a) H = p + (n : Ordinal)) ∧
    (∀ i : Nat, i < H →
      p + Ordinal.omega0 ≤ actualControlledStateAfter Phi (actualDescentStep a) i) ∧
    H % 2 = (1 + restrictedPartitionCount d (Phi (u + 1) - e)) % 2

end LogicLineages.CartierObserverCurrent.MainTheorem.Targets
