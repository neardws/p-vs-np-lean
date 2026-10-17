import PvsNP.TuringMachine
import PvsNP.Complexity
import PvsNP.Main
import PvsNP.QueryDiag
import PvsNP.PolyBound
import PvsNP.Relativization
import PvsNP.Enumeration
import PvsNP.Pairing
import PvsNP.OracleVerifiers
import PvsNP.Verifier
import PvsNP.SpaceSim
import PvsNP.TagDecide
import PvsNP.Collapse
import PvsNP.NaturalProofs
import PvsNP
open PvsNP PvsNP.Natural
#print axioms exists_oracle_diag
#print axioms OTM.unfold_eval
#print axioms queryLang_mem_OracleP
#print axioms testLang_mem_OracleNP
#print axioms testLang_not_mem_OracleP_bgs
#print axioms bgs_separation
#print axioms OracleP_subset_OracleNP
#print axioms P_subset_NP
#print axioms exists_slice_space_decider
#print axioms sliceLang_mem_OracleP_upspace
#print axioms bgs_collapse
#print axioms bgs_collapse_rawFragment
#print axioms univ_mem_OracleP
#print axioms acceptAllOTM_decides
#print axioms OracleNPRawSlice_trivial_subset_OracleP
#print axioms P_ne_NP
#print axioms tagEncode_injective
#print axioms spaceLang_iff_oracle
#print axioms tagWriting_orun
#print axioms tagQuery_after_tag
#print axioms tagQueryOTM_decides_oracle
#print axioms spaceLang_mem_OracleP
#print axioms PSPACE_subset_OracleP_tqbf
#print axioms kindLang_mem_OracleP_hardSlice
#print axioms upSliceLang_mem_OracleP_hardSlice
#print axioms const_false_has_circuit
