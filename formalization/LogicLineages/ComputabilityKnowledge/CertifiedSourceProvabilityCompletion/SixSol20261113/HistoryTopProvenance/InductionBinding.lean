module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionBinding
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel
open Induction InductionSyntax

noncomputable def allLinesElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines : Term ctx) :
 Derivation T (.imp (allLines itag ptag ctag vtag leftTag rightTag count)
   (allContext itag ptag ctag vtag leftTag rightTag count lines)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allContext itag ptag ctag vtag leftTag rightTag (liftTerm count) (.var 0)) lines)
 simpa only [GorbowPACore.logicalFormula,allLinesAt,allLines] using h

noncomputable def allContextElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context : Term ctx) :
 Derivation T (.imp (allContext itag ptag ctag vtag leftTag rightTag count lines)
   (allRaw itag ptag ctag vtag leftTag rightTag count lines context)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allRaw itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (.var 0)) context)
 simpa only [GorbowPACore.logicalFormula,allContextAt,allContext] using h

noncomputable def allRawElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw : Term ctx) :
 Derivation T (.imp (allRaw itag ptag ctag vtag leftTag rightTag count lines context)
   (allTail itag ptag ctag vtag leftTag rightTag count lines context raw)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allTail itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (.var 0)) raw)
 simpa only [GorbowPACore.logicalFormula,allRawAt,allRaw] using h

noncomputable def allTailElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail : Term ctx) :
 Derivation T (.imp (allTail itag ptag ctag vtag leftTag rightTag count lines context raw)
   (allRemaining itag ptag ctag vtag leftTag rightTag count lines context raw tail)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allRemaining itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (.var 0)) tail)
 simpa only [GorbowPACore.logicalFormula,allTailAt,allTail] using h

noncomputable def allRemainingElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining : Term ctx) :
 Derivation T (.imp (allRemaining itag ptag ctag vtag leftTag rightTag count lines context raw tail)
   (allIndex itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allIndex itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (.var 0)) remaining)
 simpa only [GorbowPACore.logicalFormula,allRemainingAt,allRemaining] using h

noncomputable def allIndexElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining index : Term ctx) :
 Derivation T (.imp (allIndex itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining)
   (allFuel itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (allFuel itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (.var 0)) index)
 simpa only [GorbowPACore.logicalFormula,allIndexAt,allIndex] using h

noncomputable def allFuelElim {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining index fuel : Term ctx) :
 Derivation T (.imp (allFuel itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index)
   (provenance itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
   (provenance itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (.var 0)) fuel)
 simpa only [GorbowPACore.logicalFormula,allFuelAt,allFuel] using h

noncomputable def atArguments {T : Sentence → Prop} {ctx : Nat} itag ptag ctag vtag leftTag rightTag
 (count lines context raw tail remaining index fuel : Term ctx) :
 Derivation T (.imp (allLines itag ptag ctag vtag leftTag rightTag count)
   (provenance itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel)) := by
 exact Hilbert.compose (allFuelElim itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel) (Hilbert.compose (allIndexElim itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index) (Hilbert.compose (allRemainingElim itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining) (Hilbert.compose (allTailElim itag ptag ctag vtag leftTag rightTag count lines context raw tail) (Hilbert.compose (allRawElim itag ptag ctag vtag leftTag rightTag count lines context raw) (Hilbert.compose (allContextElim itag ptag ctag vtag leftTag rightTag count lines context) (allLinesElim itag ptag ctag vtag leftTag rightTag count lines))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionBinding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionBinding
