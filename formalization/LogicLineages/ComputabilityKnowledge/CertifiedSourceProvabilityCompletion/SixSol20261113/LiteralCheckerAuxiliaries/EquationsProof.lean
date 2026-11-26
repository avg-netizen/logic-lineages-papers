module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FieldsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix FieldsProof
open HistoryKernel.TransitionEquationsProof (threeValues)

def leftCheck : Program 4 := applyTwo equalCode (.projection 1) contextField
def rightCheck : Program 4 := applyTwo equalCode (.projection 2) doubledRaw
def checks : Program 4 := conjunction leftCheck rightCheck
def historyGuard : Program 4 := choose historyField (constant 4 0) checks
def outerArguments : Fin 3 → Program 4 := Fin.cases optionField (Fin.cases (constant 4 0) (Fin.cases historyGuard Fin.elim0))
def historyArguments : Fin 3 → Program 4 := Fin.cases historyField (Fin.cases (constant 4 0) (Fin.cases checks Fin.elim0))
def checkArguments : Fin 3 → Program 4 := Fin.cases leftCheck (Fin.cases (constant 4 0) (Fin.cases rightCheck Fin.elim0))
def leftArguments : Fin 2 → Program 4 := Fin.cases (.projection 1) (Fin.cases contextField Fin.elim0)
def rightArguments : Fin 2 → Program 4 := Fin.cases (.projection 2) (Fin.cases doubledRaw Fin.elim0)
def historyTag (tag : Nat) := tag+argumentTag HistoryCodec.select outerArguments 2
def checksTag (tag : Nat) := historyTag tag+argumentTag HistoryCodec.select historyArguments 2
def leftTag (tag : Nat) := checksTag tag+argumentTag HistoryCodec.select checkArguments 0+1
def rightTag (tag : Nat) := checksTag tag+argumentTag HistoryCodec.select checkArguments 2+1

def normal {ctx : Nat} (tag : Nat) (context raw requested formula : Term ctx) : Term ctx :=
  call (checksTag tag+1) (HistoryKernel.pairCall (leftTag tag) requested context ::ᵥ .zero ::ᵥ
    HistoryKernel.pairCall (rightTag tag) formula (.add raw raw) ::ᵥ nil)

theorem historyInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩) :
    (nodes p)[historyTag tag]? = some ⟨4,historyGuard⟩ := Equations.argumentChild p tag HistoryCodec.select outerArguments ht 2
theorem checksInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩) :
    (nodes p)[checksTag tag]? = some ⟨4,checks⟩ := Equations.argumentChild p _ HistoryCodec.select historyArguments (historyInstalled p tag ht) 2

theorem leftEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,leftCheck⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (HistoryKernel.pairCall (tag+1) requested context))) :=
  HistoryAppend.ValueEquationsProof.binaryValues p tag equalCode leftArguments ht _ requested context
    (Equations.projection p _ (1 : Fin 4) (Equations.argumentChild p tag equalCode leftArguments ht 0) _)
    (entryPartEquation p _ ptag ctag false (Equations.argumentChild p tag equalCode leftArguments ht 1) hp hc context raw tail lines requested formula certificate)

theorem rightEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,rightCheck⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (HistoryKernel.pairCall (tag+1) formula (.add raw raw)))) :=
  HistoryAppend.ValueEquationsProof.binaryValues p tag equalCode rightArguments ht _ formula (.add raw raw)
    (Equations.projection p _ (2 : Fin 4) (Equations.argumentChild p tag equalCode rightArguments ht 0) _)
    (doubledEquation p _ ptag ctag (Equations.argumentChild p tag equalCode rightArguments ht 1) hp hc context raw tail lines requested formula certificate)

theorem checksEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (checksTag tag) (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (normal tag context raw requested formula))) := by
  have hchecks := checksInstalled p tag ht
  exact threeValues p (checksTag tag) HistoryCodec.select checkArguments hchecks _ _ .zero _
    (leftEquation p _ ptag ctag (Equations.argumentChild p _ HistoryCodec.select checkArguments hchecks 0) hp hc context raw tail lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p _ HistoryCodec.select checkArguments hchecks 1) _)
    (rightEquation p _ ptag ctag (Equations.argumentChild p _ HistoryCodec.select checkArguments hchecks 2) hp hc context raw tail lines requested formula certificate)

theorem historyEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (historyTag tag) (successfulArgs ptag ctag context raw tail lines requested formula certificate))
        (normal tag context raw requested formula))) := by
  have hh := historyInstalled p tag ht
  obtain ⟨he⟩ := threeValues p (historyTag tag) HistoryCodec.select historyArguments hh _
    (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail) .zero (normal tag context raw requested formula)
    (FieldsProof.historyEquation p _ ptag (Equations.argumentChild p _ HistoryCodec.select historyArguments hh 0) hp _ lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p _ HistoryCodec.select historyArguments hh 1) _)
    (checksEquation p tag ptag ctag ht hp hc context raw tail lines requested formula certificate)
  obtain ⟨hs⟩ := HistoryKernel.NormalProof.selectOnCons p (historyTag tag+1) ctag
    (Equations.functionChild p _ HistoryCodec.select historyArguments hh) hc (HistoryKernel.pairCall ptag context raw) tail .zero _
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem finalizerEquation {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context raw tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (finalCall tag (successfulState ptag ctag context raw tail lines) requested formula certificate)
        (normal tag context raw requested formula))) := by
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select outerArguments ht _
    (.succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)) .zero (normal tag context raw requested formula)
    (optionEquation p _ ptag (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 0) hp _ lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 1) _)
    (historyEquation p tag ptag ctag ht hp hc context raw tail lines requested formula certificate)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectPositive p (tag+1)
    (Equations.functionChild p tag HistoryCodec.select outerArguments ht) (.zero : Term ctx) _
    (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem comparisonNodes {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩) :
    (nodes p)[checksTag tag+1]? = some ⟨3,HistoryCodec.select⟩ ∧
    (nodes p)[leftTag tag]? = some ⟨2,equalCode⟩ ∧ (nodes p)[rightTag tag]? = some ⟨2,equalCode⟩ := by
  have hc := checksInstalled p tag ht
  exact ⟨Equations.functionChild p _ HistoryCodec.select checkArguments hc,
    Equations.functionChild p _ equalCode leftArguments (Equations.argumentChild p _ HistoryCodec.select checkArguments hc 0),
    Equations.functionChild p _ equalCode rightArguments (Equations.argumentChild p _ HistoryCodec.select checkArguments hc 2)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.EquationsProof
