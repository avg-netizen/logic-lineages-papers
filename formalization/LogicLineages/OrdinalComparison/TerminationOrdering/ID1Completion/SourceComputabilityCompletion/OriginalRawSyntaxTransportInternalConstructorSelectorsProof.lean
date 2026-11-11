module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual nested equality tests select arity 0 at literal tag 0. -/
theorem arityTag0 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 0) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) := by
  apply branchNumeralIntro 0 1 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 0 4 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 0 2 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 0 5 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 0 7 (leftOf query) _ _ (numeral 0) xs ht
  exact constantValue 0 xs

theorem variableArity {n : Nat} (query : Program n) (raw index : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph variableConstructor raw (Fin.cons index Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) :=
  arityTag0 query xs (variableTag query raw index xs hq hc)

/-- The actual nested equality tests select arity 1 at literal tag 1. -/
theorem arityTag1 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 1) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 1) xs)) := by
  apply branchNumeralIntro 1 1 (leftOf query) _ _ (numeral 1) xs ht
  exact constantValue 1 xs

theorem lambdaArity {n : Nat} (query : Program n) (raw domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 1) xs)) :=
  arityTag1 query xs (lambdaTag query raw domain child xs hq hc)

theorem lambdaFirst {n : Nat} (query : Program n) (raw domain child : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) child xs)) := by
  have ht := lambdaTag query raw domain child xs hq hc
  apply branchNumeralIntro 1 1 (leftOf query) _ _ child xs ht
  exact lambdaBody query raw domain child xs hq hc

/-- The actual nested equality tests select arity 2 at literal tag 2. -/
theorem arityTag2 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 2) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) := by
  apply branchNumeralIntro 2 1 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 2 4 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 2 2 (leftOf query) _ _ (numeral 2) xs ht
  exact constantValue 2 xs

theorem applicationArity {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) :=
  arityTag2 query xs (applicationTag query raw domain fn arg xs hq hc)

theorem applicationFirst {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) fn xs)) := by
  have ht := applicationTag query raw domain fn arg xs hq hc
  apply branchNumeralIntro 2 1 (leftOf query) _ _ fn xs ht
  apply branchNumeralIntro 2 4 (leftOf query) _ _ fn xs ht
  apply branchNumeralIntro 2 5 (leftOf query) _ _ fn xs ht
  exact applicationFunction query raw domain fn arg xs hq hc

theorem applicationSecond {n : Nat} (query : Program n) (raw domain fn arg : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) arg xs)) := by
  apply branchNumeralIntro 2 5 (leftOf query) _ _ arg xs
    (applicationTag query raw domain fn arg xs hq hc)
  exact applicationArgument query raw domain fn arg xs hq hc

/-- The actual nested equality tests select arity 0 at literal tag 3. -/
theorem arityTag3 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 3) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) := by
  apply branchNumeralIntro 3 1 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 3 4 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 3 2 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 3 5 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 3 7 (leftOf query) _ _ (numeral 0) xs ht
  exact constantValue 0 xs

theorem bottomArity {n : Nat} (query : Program n) (raw tau : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) :=
  arityTag3 query xs (bottomTag query raw tau xs hq hc)

/-- The actual nested equality tests select arity 1 at literal tag 4. -/
theorem arityTag4 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 4) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 1) xs)) := by
  apply branchNumeralIntro 4 1 (leftOf query) _ _ (numeral 1) xs ht
  apply branchNumeralIntro 4 4 (leftOf query) _ _ (numeral 1) xs ht
  exact constantValue 1 xs

theorem ordinaryArity {n : Nat} (query : Program n) (raw head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 1) xs)) :=
  arityTag4 query xs (ordinaryTag query raw head base xs hq hc)

theorem ordinaryFirst {n : Nat} (query : Program n) (raw head base : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0))))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) base xs)) := by
  have ht := ordinaryTag query raw head base xs hq hc
  apply branchNumeralIntro 4 1 (leftOf query) _ _ base xs ht
  apply branchNumeralIntro 4 4 (leftOf query) _ _ base xs ht
  exact ordinaryBase query raw head base xs hq hc

/-- The actual nested equality tests select arity 2 at literal tag 5. -/
theorem arityTag5 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 5) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) := by
  apply branchNumeralIntro 5 1 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 5 4 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 5 2 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 5 5 (leftOf query) _ _ (numeral 2) xs ht
  exact constantValue 2 xs

theorem numberedArity {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) :=
  arityTag5 query xs (numberedTag query raw label head tau base types extras xs hq hc)

theorem numberedFirst {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) base xs)) := by
  have ht := numberedTag query raw label head tau base types extras xs hq hc
  apply branchNumeralIntro 5 1 (leftOf query) _ _ base xs ht
  apply branchNumeralIntro 5 4 (leftOf query) _ _ base xs ht
  apply branchNumeralIntro 5 5 (leftOf query) _ _ base xs ht
  exact numberedBase query raw label head tau base types extras xs hq hc

theorem numberedSecond {n : Nat} (query : Program n) (raw label head tau base types extras : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) extras xs)) := by
  apply branchNumeralIntro 5 5 (leftOf query) _ _ extras xs
    (numberedTag query raw label head tau base types extras xs hq hc)
  exact numberedExtras query raw label head tau base types extras xs hq hc

/-- The actual nested equality tests select arity 0 at literal tag 6. -/
theorem arityTag6 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 6) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) := by
  apply branchNumeralIntro 6 1 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 6 4 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 6 2 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 6 5 (leftOf query) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 6 7 (leftOf query) _ _ (numeral 0) xs ht
  exact constantValue 0 xs

theorem nilArity {n : Nat} (query : Program n) (raw  : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph nilConstructor raw (Fin.elim0)))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 0) xs)) :=
  arityTag6 query xs (nilTag query raw  xs hq hc)

/-- The actual nested equality tests select arity 2 at literal tag 7. -/
theorem arityTag7 {n : Nat} (query : Program n) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 7) xs))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) := by
  apply branchNumeralIntro 7 1 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 7 4 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 7 2 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 7 5 (leftOf query) _ _ (numeral 2) xs ht
  apply branchNumeralIntro 7 7 (leftOf query) _ _ (numeral 2) xs ht
  exact constantValue 2 xs

theorem consArity {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (arityOf query) (numeral 2) xs)) :=
  arityTag7 query xs (consTag query raw tau head tail xs hq hc)

theorem consFirst {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (firstOf query) head xs)) := by
  have ht := consTag query raw tau head tail xs hq hc
  apply branchNumeralIntro 7 1 (leftOf query) _ _ head xs ht
  apply branchNumeralIntro 7 4 (leftOf query) _ _ head xs ht
  apply branchNumeralIntro 7 5 (leftOf query) _ _ head xs ht
  exact consHead query raw tau head tail xs hq hc

theorem consSecond {n : Nat} (query : Program n) (raw tau head tail : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0)))))) :
    Nonempty (Derivation body Delta (programGraph (secondOf query) tail xs)) := by
  apply branchNumeralIntro 7 5 (leftOf query) _ _ tail xs
    (consTag query raw tau head tail xs hq hc)
  exact consTail query raw tau head tail xs hq hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
