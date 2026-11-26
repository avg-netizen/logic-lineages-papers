module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorDormantSelectorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-! Exact total selector behavior in positions never visited by the machine:
both leaf selectors and the second selector of a unary constructor. -/

theorem variableFirstForward {n : Nat} (query : Program n) (raw out index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out index)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := variableIndex query raw index xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) index Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := variableTag query raw index xs hq hc
  have h1 := branchNumeralElim 0 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 0 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 0 5 (leftOf query) _ _ out xs ht h4
  exact (substitutionGraph hsub (Fin.cons index Fin.elim0) xs out hg).mpr h5

theorem variableFirstBackward {n : Nat} (query : Program n) (raw out index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out index))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := variableIndex query raw index xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) index Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := variableTag query raw index xs hq hc
  apply branchNumeralIntro 0 1 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 0 4 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 0 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons index Fin.elim0) xs out hg).mp ho

theorem variableSecondForward {n : Nat} (query : Program n) (raw out index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out index)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := variableIndex query raw index xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) index Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := variableTag query raw index xs hq hc
  have h5 := branchNumeralElim 0 5 (leftOf query) _ _ out xs ht ho
  exact (substitutionGraph hsub (Fin.cons index Fin.elim0) xs out hg).mpr h5

theorem variableSecondBackward {n : Nat} (query : Program n) (raw out index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out index))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := variableIndex query raw index xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) index Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := variableTag query raw index xs hq hc
  apply branchNumeralIntro 0 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons index Fin.elim0) xs out hg).mp ho

theorem bottomFirstForward {n : Nat} (query : Program n) (raw out tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out tau)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := bottomType query raw tau xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) tau Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := bottomTag query raw tau xs hq hc
  have h1 := branchNumeralElim 3 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 3 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 3 5 (leftOf query) _ _ out xs ht h4
  exact (substitutionGraph hsub (Fin.cons tau Fin.elim0) xs out hg).mpr h5

theorem bottomFirstBackward {n : Nat} (query : Program n) (raw out tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out tau))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := bottomType query raw tau xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) tau Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := bottomTag query raw tau xs hq hc
  apply branchNumeralIntro 3 1 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 3 4 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 3 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons tau Fin.elim0) xs out hg).mp ho

theorem bottomSecondForward {n : Nat} (query : Program n) (raw out tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out tau)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := bottomType query raw tau xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) tau Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := bottomTag query raw tau xs hq hc
  have h5 := branchNumeralElim 3 5 (leftOf query) _ _ out xs ht ho
  exact (substitutionGraph hsub (Fin.cons tau Fin.elim0) xs out hg).mpr h5

theorem bottomSecondBackward {n : Nat} (query : Program n) (raw out tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out tau))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := bottomType query raw tau xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) tau Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := bottomTag query raw tau xs hq hc
  apply branchNumeralIntro 3 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons tau Fin.elim0) xs out hg).mp ho

theorem nilFirstForward {n : Nat} (query : Program n) (raw out  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out (numeral 0))) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := nilPayload query raw  xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) (numeral 0) Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := nilTag query raw  xs hq hc
  have h1 := branchNumeralElim 6 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 6 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 6 5 (leftOf query) _ _ out xs ht h4
  exact (substitutionGraph hsub (Fin.cons (numeral 0) Fin.elim0) xs out hg).mpr h5

theorem nilFirstBackward {n : Nat} (query : Program n) (raw out  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (leftOf (rightOf (.projection 0))) out (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.left
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := nilPayload query raw  xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) (numeral 0) Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := nilTag query raw  xs hq hc
  apply branchNumeralIntro 6 1 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 6 4 (leftOf query) _ _ out xs ht
  apply branchNumeralIntro 6 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons (numeral 0) Fin.elim0) xs out hg).mp ho

theorem nilSecondForward {n : Nat} (query : Program n) (raw out  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out (numeral 0))) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := nilPayload query raw  xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) (numeral 0) Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := nilTag query raw  xs hq hc
  have h5 := branchNumeralElim 6 5 (leftOf query) _ _ out xs ht ho
  exact (substitutionGraph hsub (Fin.cons (numeral 0) Fin.elim0) xs out hg).mpr h5

theorem nilSecondBackward {n : Nat} (query : Program n) (raw out  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph1 (rightOf (rightOf (.projection 0))) out (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) out xs)) := by
  let gs : Fin 1 → Program n := fun _ => rightOf query
  have hsub : Substitutes gs (rightOf (rightOf (.projection 0))) (rightOf (rightOf (rightOf query))) :=
    unarySubstitution InternalUnpair.right
      (unarySubstitution InternalUnpair.right (Substitutes.projection 0))
  have hp := nilPayload query raw  xs hq hc
  have hg : ∀ i : Fin 1, Nonempty (Derivation body Delta
      (programGraph (gs i) ((Fin.cons (α := fun _ => OTerm alpha) (numeral 0) Fin.elim0) i) xs)) := by
    intro i
    obtain rfl := Fin.eq_zero i
    exact hp
  have ht := nilTag query raw  xs hq hc
  apply branchNumeralIntro 6 5 (leftOf query) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons (numeral 0) Fin.elim0) xs out hg).mp ho

theorem lambdaSecondForward {n : Nat} (query : Program n) (raw out domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right out child)) := by
  have ht := lambdaTag query raw domain child xs hq hc
  have hp := lambdaBody query raw domain child xs hq hc
  have h5 := branchNumeralElim 1 5 (leftOf query) _ _ out xs ht ho
  exact unaryRecover InternalUnpair.right (rightOf (rightOf query)) out child xs h5 hp

theorem lambdaSecondBackward {n : Nat} (query : Program n) (raw out domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.right out child))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) out xs)) := by
  have ht := lambdaTag query raw domain child xs hq hc
  have hp := lambdaBody query raw domain child xs hq hc
  apply branchNumeralIntro 1 5 (leftOf query) _ _ out xs ht
  exact unaryValue InternalUnpair.right (rightOf (rightOf query)) out child xs ho hp

theorem ordinarySecondForward {n : Nat} (query : Program n) (raw out head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right out base)) := by
  have ht := ordinaryTag query raw head base xs hq hc
  have hp := ordinaryBase query raw head base xs hq hc
  have h5 := branchNumeralElim 4 5 (leftOf query) _ _ out xs ht ho
  exact unaryRecover InternalUnpair.right (rightOf (rightOf query)) out base xs h5 hp

theorem ordinarySecondBackward {n : Nat} (query : Program n) (raw out head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.right out base))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) out xs)) := by
  have ht := ordinaryTag query raw head base xs hq hc
  have hp := ordinaryBase query raw head base xs hq hc
  apply branchNumeralIntro 4 5 (leftOf query) _ _ out xs ht
  exact unaryValue InternalUnpair.right (rightOf (rightOf query)) out base xs ho hp

/-- Both dormant selectors of the literal nil constructor return zero. -/
theorem nilFirstZero {n : Nat} (query : Program n) (raw : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) (numeral 0) xs)) := by
  let zs : Fin 1 → OTerm alpha := Fin.cons (numeral 0) Fin.elim0
  have hr : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (numeral 0 : OTerm alpha) (numeral 0))) :=
    pairRight (numeral 0) (numeral 0) (numeral 0)
      InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hd : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left (numeral 0 : OTerm alpha) (numeral 0))) :=
    pairLeft (numeral 0) (numeral 0) (numeral 0)
      InternalApplicationValidityStackAppendTransitionProof.pairZero
  apply nilFirstBackward query raw (numeral 0) xs hq hc
  exact unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 0) (numeral 0) zs hd
    (unaryValue InternalUnpair.right (.projection 0) (numeral 0) (numeral 0) zs hr (projectionValue 0 zs))

/-- Both dormant selectors of the literal nil constructor return zero. -/
theorem nilSecondZero {n : Nat} (query : Program n) (raw : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) (numeral 0) xs)) := by
  let zs : Fin 1 → OTerm alpha := Fin.cons (numeral 0) Fin.elim0
  have hr : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (numeral 0 : OTerm alpha) (numeral 0))) :=
    pairRight (numeral 0) (numeral 0) (numeral 0)
      InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hd : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (numeral 0 : OTerm alpha) (numeral 0))) :=
    pairRight (numeral 0) (numeral 0) (numeral 0)
      InternalApplicationValidityStackAppendTransitionProof.pairZero
  apply nilSecondBackward query raw (numeral 0) xs hq hc
  exact unaryValue InternalUnpair.right (rightOf (.projection 0)) (numeral 0) (numeral 0) zs hd
    (unaryValue InternalUnpair.right (.projection 0) (numeral 0) (numeral 0) zs hr (projectionValue 0 zs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorDormantSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorDormantSelectorsProof
