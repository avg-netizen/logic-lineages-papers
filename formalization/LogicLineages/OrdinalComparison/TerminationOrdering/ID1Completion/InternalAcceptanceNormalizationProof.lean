module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalAcceptanceSupportProof InternalControlGraphSupportProof InternalControlGraphProof
open InternalControlGraphValueProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem normalizeValue {n : Nat} (p : Program n) (out v : OTerm α) (xs : Fin n → OTerm α)
    (ht : Nonempty (Derivation body Gamma (programGraph equalsOne out (Fin.cons v Fin.elim0))))
    (hp : Nonempty (Derivation body Gamma (programGraph p v xs))) :
    Nonempty (Derivation body Gamma (programGraph (normalize p) out xs)) := by
  apply compositionValue equalsOne (fun _ : Fin 1 => p) out xs (Fin.cons v Fin.elim0) ht
  intro i
  obtain rfl := Fin.eq_zero i
  exact hp

theorem normalizeAccept {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph (normalize p) (suc z) xs)) :=
  normalizeValue p (suc z) (suc z) xs equalsOneOneValue hp

/-- The full equals-one graph excludes its rejecting disjunct at output ONE. -/
theorem equalsOneAcceptInput (input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph equalsOne (suc z) (Fin.cons input Fin.elim0)))) :
    Nonempty (Derivation body Gamma (eqn input (suc z))) := by
  obtain ⟨d⟩ := actualOriginalEqualsOneGraph body α (suc z) input
  obtain ⟨h⟩ := h
  have ds := Derivation.implicationElimination
    (weakenClosed (Derivation.conjunctionLeft d) Gamma) h
  change Derivation body Gamma
    ((equal input (suc z) ⊓ equal (suc z) (suc z)) ⊔
      ((equal input (suc z)).not ⊓ equal (suc z) z)) at ds
  simp only [equalEqn] at ds
  exact ⟨disjunctionElimination ds
    (Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (Derivation.explosion
      (sucNeZeroApply (Derivation.conjunctionRight
        (Derivation.hypothesis List.mem_cons_self)))))⟩

theorem normalizeRecover {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph (normalize p) (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph p (suc z) xs)) := by
  apply programCompositionCases equalsOne (fun _ : Fin 1 => p) (suc z) xs _ hp
  intro β j ys Delta _ ht hg
  simp only [programRename,sucRelabel,zRelabel]
  simp only [sucRelabel,zRelabel] at ht
  rw [← oneTuple ys] at ht
  exact outputTransport p (ys 0) (suc z) (fun i => (xs i).relabel j)
    (equalsOneAcceptInput (ys 0) ht) (hg 0)

/-- Internal failure of exact-one acceptance yields the normalizer's zero graph. -/
theorem normalizeReject {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph p (suc z) xs).not)) :
    Nonempty (Derivation body Gamma (programGraph (normalize p) z xs)) := by
  apply programCases p xs _
  intro β j Delta v hj hv
  simp only [programRename,zRelabel]
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta ((programGraph p (suc z) xs).relabel j).not) at hn'
  simp only [programRename,sucRelabel,zRelabel] at hn'
  obtain ⟨hn'⟩ := hn'
  obtain ⟨hv⟩ := hv
  have he : Nonempty (Derivation body Delta (eqn v (suc z)).not) := by
    obtain ⟨ha⟩ := outputTransport p v (suc z) (fun i => (xs i).relabel j)
      (show Nonempty (Derivation body (eqn v (suc z) :: Delta) (eqn v (suc z))) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
      ⟨addHyp hv _⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn' _) ha)⟩
  exact normalizeValue p z v (fun i => (xs i).relabel j) (equalsOneAtNonone v he) ⟨hv⟩

theorem actualOriginalNormalizationAcceptance :
    InternalAcceptanceTargets.ActualOriginalNormalizationAcceptance := by
  intro body n p α xs
  obtain ⟨hf⟩ := normalizeRecover (body := body)
    (Gamma := [programGraph (normalize p) (suc z) xs]) p xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := normalizeAccept (body := body)
    (Gamma := [programGraph p (suc z) xs]) p xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
