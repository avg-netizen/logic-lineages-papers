module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof (substPair)

theorem substFields {m n : Nat} (sub : Fin m → Term n) vtag leftTag rightTag (line context raw : Term m) :
 substituteFormula sub (lineFields vtag leftTag rightTag line context raw) =
 lineFields vtag leftTag rightTag (substitute sub line) (substitute sub context) (substitute sub raw) := by
 simp only [lineFields,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem substWitness {m n : Nat} (sub : Fin m → Term n) vtag leftTag rightTag (context raw : Term m) :
 substituteFormula sub (topWitness vtag leftTag rightTag context raw) =
 topWitness vtag leftTag rightTag (substitute sub context) (substitute sub raw) := by
 simp only [topWitness,substituteFormula,substFields,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem fieldsAt {ctx : Nat} vtag leftTag rightTag (line context raw : Term ctx) :
 GorbowStandardInstances.instantiate
   (lineFields vtag leftTag rightTag (.var 0) (liftTerm context) (liftTerm raw)) line =
 lineFields vtag leftTag rightTag line context raw := by
 simp only [GorbowStandardInstances.instantiate,substFields,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} vtag leftTag rightTag (line context raw : Term ctx) :
 Derivation T (.imp (lineFields vtag leftTag rightTag line context raw) (topWitness vtag leftTag rightTag context raw)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T)
   (lineFields vtag leftTag rightTag (.var 0) (liftTerm context) (liftTerm raw)) line
 rw [fieldsAt] at h
 exact h

theorem substProvenance {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag
 (count lines context raw tail remaining index fuel : Term m) :
 substituteFormula sub (provenance itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel) =
 provenance itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines)
   (substitute sub context) (substitute sub raw) (substitute sub tail) (substitute sub remaining)
   (substitute sub index) (substitute sub fuel) := by
 simp only [provenance,substituteFormula,HistoryRunSplice.IdleProof.substRun,
   HistoryRunSplice.PrefixSupportProof.substState,HistoryLookup.DropEquationsProof.substCons,
   substPair,substWitness,substitute]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
