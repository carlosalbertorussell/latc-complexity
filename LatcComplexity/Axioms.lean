import LatcComplexity.Bridge
import LatcComplexity.General

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
