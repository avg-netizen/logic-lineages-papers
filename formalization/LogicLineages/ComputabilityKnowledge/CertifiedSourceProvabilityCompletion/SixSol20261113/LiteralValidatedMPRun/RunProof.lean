module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP

theorem internalTrailingStep : Targets.InternalTrailingStep := by
 intro l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hv⟩ := ValidityProof.internalNewLineValidity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 obtain ⟨hstep⟩ := LiteralMPRun.TrailingProof.internalTrailingStep validity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hstep) hh) (.mp (.base hv) hh)))⟩

theorem internalConstructedRun : Targets.InternalConstructedRun := by
 intro l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag hm ctx context phi psi imp ant tailI tailA index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hv⟩ := ValidityProof.internalNewLineValidity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 obtain ⟨hstep⟩ := LiteralMPRun.ConstructedProof.internalConstructedRun validity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag hm ctx context phi psi imp ant tailI tailA index fuel
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hstep) hh) (.mp (.base hv) hh)))⟩

theorem internalCoreAcceptance : Targets.InternalCoreAcceptance := by
 intro l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag qtag hm hq ctx context phi psi imp ant tailI tailA index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hv⟩ := ValidityProof.internalNewLineValidity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 obtain ⟨hstep⟩ := LiteralMPRun.CoreProof.internalCoreAcceptance validity l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag qtag hm hq ctx context phi psi imp ant tailI tailA index fuel
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base hstep) hh) (.mp (.base hv) hh)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.RunProof
