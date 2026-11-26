module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant sameOf)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalTypedDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-context disjunction elimination; no arithmetic semantics is used. -/
theorem orCases {p q psi : Formula alpha}
    (h : Nonempty (Derivation body Delta (p ⊔ q)))
    (hp : Nonempty (Derivation body (p :: Delta) psi))
    (hq : Nonempty (Derivation body (q :: Delta) psi)) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨InternalBetaTotalityProof.disjunctionElimination h
    (Derivation.implicationIntroduction hp) (Derivation.implicationIntroduction hq)⟩

theorem sameAcceptAt {n : Nat} (p q : Program n) (x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (he : Nonempty (Derivation body Delta (equal x y))) :
    Nonempty (Derivation body Delta (programGraph (sameOf p q) (numeral 1) xs)) := by
  have he' : Nonempty (Derivation body Delta (eqn x y)) := by
    simpa only [equalEqn,numeral] using he
  obtain ⟨he'⟩ := he'
  exact InternalApplicationStepPeelSupportProof.sameAccept p q x xs hp
    (outputTransport q y x xs ⟨symm he'⟩ hq)

theorem sameYesIntro {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (he : Nonempty (Derivation body Delta (equal x y)))
    (ho : Nonempty (Derivation body Delta (programGraph yes out xs))) :
    Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs)) :=
  successorBranchIntro _ no yes out z xs (sameAcceptAt p q x y xs hp hq he) ho

theorem sameYesElim {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (he : Nonempty (Derivation body Delta (equal x y)))
    (ho : Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs))) :
    Nonempty (Derivation body Delta (programGraph yes out xs)) :=
  successorBranchElim _ no yes out z xs (sameAcceptAt p q x y xs hp hq he) ho

theorem sameNoIntro {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (he : Nonempty (Derivation body Delta (equal x y).not))
    (ho : Nonempty (Derivation body Delta (programGraph no out xs))) :
    Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs)) :=
  zeroBranchIntro _ no yes out xs (sameReject p q x y xs hp hq he) ho

theorem sameNoElim {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (he : Nonempty (Derivation body Delta (equal x y).not))
    (ho : Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs))) :
    Nonempty (Derivation body Delta (programGraph no out xs)) :=
  zeroBranchElim _ no yes out xs (sameReject p q x y xs hp hq he) ho

/-- Exact all-output elimination of one literal equality branch. -/
theorem sameForward {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs))) :
    Nonempty (Derivation body Delta
      ((equal x y ⊓ programGraph yes out xs) ⊔
        ((equal x y).not ⊓ programGraph no out xs))) := by
  apply formulaCases (equal x y) _
  · have he : Nonempty (Derivation body (equal x y :: Delta) (equal x y)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hy⟩ := sameYesElim p q yes no out x y xs
      (withHyp hp _) (withHyp hq _) he (withHyp ho _)
    exact ⟨orLeft (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self) hy)⟩
  · have he : Nonempty (Derivation body ((equal x y).not :: Delta) (equal x y).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hn⟩ := sameNoElim p q yes no out x y xs
      (withHyp hp _) (withHyp hq _) he (withHyp ho _)
    exact ⟨orRight (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self) hn)⟩

/-- Exact all-output introduction of one literal equality branch. -/
theorem sameBackward {n : Nat} (p q yes no : Program n) (out x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (ho : Nonempty (Derivation body Delta
      ((equal x y ⊓ programGraph yes out xs) ⊔
        ((equal x y).not ⊓ programGraph no out xs)))) :
    Nonempty (Derivation body Delta (programGraph (ifSame p q yes no) out xs)) := by
  apply orCases ho
  · exact sameYesIntro p q yes no out x y xs (withHyp hp _) (withHyp hq _)
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  · exact sameNoIntro p q yes no out x y xs (withHyp hp _) (withHyp hq _)
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem constantForward {n : Nat} (value : Nat) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (constant n value) out xs))) :
    Nonempty (Derivation body Delta (equal out (numeral value))) := by
  simpa only [equalEqn] using valueUnique (constant n value) out (numeral value) xs h
    (constantValue value xs)

theorem constantBackward {n : Nat} (value : Nat) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation body Delta (equal out (numeral value)))) :
    Nonempty (Derivation body Delta (programGraph (constant n value) out xs)) := by
  have he : Nonempty (Derivation body Delta (eqn out (numeral value))) := by
    simpa only [equalEqn] using h
  obtain ⟨he⟩ := he
  exact outputTransport (constant n value) (numeral value) out xs ⟨symm he⟩
    (constantValue value xs)

theorem zeroAtIntro {n : Nat} (control yes no : Program n) (out c : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (he : Nonempty (Derivation body Delta (equal c (numeral 0))))
    (ho : Nonempty (Derivation body Delta (programGraph yes out xs))) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control yes no) out xs)) := by
  have he' : Nonempty (Derivation body Delta (eqn c z)) := by simpa only [equalEqn,numeral] using he
  exact zeroBranchIntro control yes no out xs (outputTransport control c z xs he' hc) ho

theorem zeroAtElim {n : Nat} (control yes no : Program n) (out c : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (he : Nonempty (Derivation body Delta (equal c (numeral 0))))
    (ho : Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control yes no) out xs))) :
    Nonempty (Derivation body Delta (programGraph yes out xs)) := by
  have he' : Nonempty (Derivation body Delta (eqn c z)) := by simpa only [equalEqn,numeral] using he
  exact zeroBranchElim control yes no out xs (outputTransport control c z xs he' hc) ho

theorem nonzeroAtIntro {n : Nat} (control no yes : Program n) (out c : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (he : Nonempty (Derivation body Delta (equal c (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (programGraph yes out xs))) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control no yes) out xs)) := by
  apply nonzeroBranchIntro control no yes out c xs hc
  · simpa only [equalEqn,numeral] using he
  · exact ho

theorem nonzeroAtElim {n : Nat} (control no yes : Program n) (out c : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (he : Nonempty (Derivation body Delta (equal c (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control no yes) out xs))) :
    Nonempty (Derivation body Delta (programGraph yes out xs)) := by
  apply nonzeroBranchElim control no yes out c xs hc
  · simpa only [equalEqn,numeral] using he
  · exact ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
