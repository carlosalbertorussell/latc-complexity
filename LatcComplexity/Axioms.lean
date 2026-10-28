import LatcComplexity.Bridge
import LatcComplexity.General
import LatcComplexity.Adequacy
import LatcComplexity.Counting

/-! Axiom audit: each theorem should depend only on `propext`, `Classical.choice` and
`Quot.sound`. -/

-- Boolean domains (`LatcComplexity/Bridge.lean`)
#print axioms Latc.PaperD.holdsAll_eq_eval
#print axioms Latc.PaperD.satisfiable_decode_iff
#print axioms Latc.PaperD.fromSAT_polyTime
#print axioms Latc.PaperD.SAT_reduces
#print axioms Latc.PaperD.MissingNonempty_npHard
#print axioms Latc.PaperD.Complete_coNPHard
#print axioms Latc.PaperD.tupleOf_polyTime
#print axioms Latc.PaperD.verifier_polyTime
#print axioms Latc.PaperD.isVerifier
#print axioms Latc.PaperD.MissingNonempty_mem_NP
#print axioms Latc.PaperD.MissingNonempty_npComplete
#print axioms Latc.PaperD.Complete_coNPComplete
#print axioms Latc.PaperD.countMissing_fromSAT
#print axioms Latc.PaperD.countMissing_sharpPHard

-- General finite domains (`LatcComplexity/General.lean`)
#print axioms Latc.PaperD.General.inDomainsB_iff
#print axioms Latc.PaperD.General.condHoldsB_iff
#print axioms Latc.PaperD.General.check_iff
#print axioms Latc.PaperD.General.check_polyTime
#print axioms Latc.PaperD.General.length_encList_le_of_inDomains
#print axioms Latc.PaperD.General.MissingNonempty_mem_NP
#print axioms Latc.PaperD.General.fromSAT_polyTime
#print axioms Latc.PaperD.General.satisfiable_iff
#print axioms Latc.PaperD.General.SAT_reduces
#print axioms Latc.PaperD.General.MissingNonempty_npHard
#print axioms Latc.PaperD.General.MissingNonempty_npComplete
#print axioms Latc.PaperD.General.Complete_coNPComplete

-- Adequacy to latc-check's `Finset` model (`LatcComplexity/Adequacy.lean`)
#print axioms Latc.PaperD.General.Inst.toList_injective
#print axioms Latc.PaperD.General.Inst.inDomains_toList
#print axioms Latc.PaperD.General.Inst.exists_toList_eq
#print axioms Latc.PaperD.General.con_cond_iff
#print axioms Latc.PaperD.General.con_iff
#print axioms Latc.PaperD.General.mem_missing_iff
#print axioms Latc.PaperD.General.mem_MissingNonempty_iff
#print axioms Latc.PaperD.General.mem_Complete_iff
#print axioms Latc.PaperD.General.coe_missing_map_toList
#print axioms Latc.PaperD.General.missingNonempty_finset_npComplete
#print axioms Latc.PaperD.General.complete_finset_coNPComplete

-- #P membership and #P-completeness of counting |M(T₀)| (`LatcComplexity/Counting.lean`)
#print axioms Latc.PaperD.rowClause_polyTime
#print axioms Latc.PaperD.toSharpSAT_polyTime
#print axioms Latc.PaperD.mem_vars_toSharpSAT
#print axioms Latc.PaperD.any_zip_iff
#print axioms Latc.PaperD.eval_toSharpSAT
#print axioms Latc.PaperD.countMissing_eq_sharpSAT
#print axioms Latc.PaperD.countMissing_reduces_sharpSAT
#print axioms Latc.PaperD.countMissing_mem_SharpP
#print axioms Latc.PaperD.countMissing_sharpPComplete
