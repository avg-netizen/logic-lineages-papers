module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedAuxiliaryCoding

theorem labelsIff {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ L,LabelsAtMost L q ↔ maxLabel q≤L := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ L,ArgumentLabelsAtMost L args ↔ argumentsMaxLabel args≤L)
  case var => intro L; simp [LabelsAtMost,maxLabel]
  case lam body ih => exact ih
  case app q a ihq iha => intro L; exact (and_congr (ihq L) (iha L)).trans (Nat.max_le).symm
  case bottom => intro L; simp [LabelsAtMost,maxLabel]
  case ordinary f base ih => exact ih
  case numbered k f tau base types extras ihb ihe =>
    intro L
    simpa only [LabelsAtMost,maxLabel,Nat.max_le] using (and_congr (Iff.rfl : k≤L ↔ k≤L) (and_congr (ihb L) (ihe L)))
  case nil => simp [ArgumentLabelsAtMost,argumentsMaxLabel]
  case cons Gamma sigma types q rest ihq ihr L =>
    exact (and_congr (ihq L) (ihr L)).trans (Nat.max_le).symm

theorem argumentLabels {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (L : Nat) (args : AuxArguments Symbol arity Gamma types) :
    ArgumentLabelsAtMost L args ↔ ∀ q∈argumentList args,LabelsAtMost L q.2 := by
  induction types with
  | nil => cases args; simp [ArgumentLabelsAtMost,argumentList]
  | cons sigma types ih => cases args with
    | cons q rest =>
      constructor
      · intro h p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact h.1
        · exact (ih rest).mp h.2 p hp
      · intro h
        exact ⟨h _ (List.mem_cons_self ..),(ih rest).mpr (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

theorem permutationLabels {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (L : Nat) (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (hp : (argumentList a).Perm (argumentList b)) : ArgumentLabelsAtMost L a ↔ ArgumentLabelsAtMost L b := by
  rw [argumentLabels,argumentLabels]
  exact ⟨fun h q hq => h q (hp.mem_iff.mpr hq),fun h q hq => h q (hp.mem_iff.mp hq)⟩

theorem primaryLabels {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (L : Nat) {q r : Packed Symbol arity Gamma} (h : Primary Symbol arity Gamma q r) :
    LabelsAtMost L q.2 ↔ LabelsAtMost L r.2 := by
  induction h using Primary.rec
    (motive_2 := fun Gamma types a b _ => ArgumentLabelsAtMost L a ↔ ArgumentLabelsAtMost L b)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  case ordinary f g base target he ht hp => exact permutationLabels L base target hp
  case numbered k f g tau base target types extras he hp =>
    exact and_congr Iff.rfl (and_congr (permutationLabels L base target hp) Iff.rfl)
  case lam q r h ih => exact ih
  case appFunction q r a h ih => exact and_congr ih Iff.rfl
  case appArgument q a b h ih => exact and_congr Iff.rfl ih
  case ordinaryArguments f base target h ih => exact ih
  case numberedBase k f tau base target types extras h ih => exact and_congr Iff.rfl (and_congr ih Iff.rfl)
  case numberedExtras k f tau base types extras target h ih => exact and_congr Iff.rfl (and_congr Iff.rfl ih)
  case nil => rfl
  case cons q r rest target hq hr ihq ihr => exact and_congr ihq ihr

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingSupportProof
